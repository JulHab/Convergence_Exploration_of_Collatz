#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
verify_certificate.py (updated)

Adds a CROSS-PLATFORM, RAM-safe coverage check.

What this script now can do:

1) Validate bucket witnesses:
   - range checks
   - prune_check(a,t,b) validity
   - rolling BLAKE2b commitments (roll + xor)
   - SHA256 of files

2) Build a disk-backed *key index* from the bucket file:
   - key := (depth << MOD_BITS) | n_mod   (fits in uint64 for MOD_BITS=40, depth<=300)
   - writes a sorted, deduplicated uint64 file: bucket_keys_u64.sorted.uniq.bin
   - done via chunk sort + k-way merge (no GNU sort, works on Windows/Linux)

3) Coverage check:
   For every seed s in [0, 2^INIT_BITS):
     - if s is in uncovered set => OK
     - else follow the deterministic residue evolution (n_mod, depth) for j=0..K
       and check whether (j, n_mod) exists in the key index.
     - If never hits by K => FAIL

Outputs:
  - bucket_acceptance.json (as before)
  - coverage_report.json   (new, when --check-coverage)

NOTE:
- This checks the missing logical piece: completeness/coverage of the certificate,
  not just validity of individual witnesses.
"""

import argparse
import gzip
import hashlib
import json
import mmap
import os
import struct
import sys
import tempfile
import time
from dataclasses import dataclass
from heapq import heappush, heappop
from typing import Dict, Iterator, List, Optional, Tuple

# -----------------------------
# Hash utilities
# -----------------------------

def blake2b(digest_size: int) -> "hashlib._Hash":
    return hashlib.blake2b(digest_size=digest_size)

def roll_hex_digest(current_roll_hex: str, new_hex: str, digest_size: int) -> str:
    h = blake2b(digest_size=digest_size)
    if current_roll_hex:
        h.update(bytes.fromhex(current_roll_hex))
    h.update(bytes.fromhex(new_hex))
    return h.hexdigest()

def xor_hex_digest(current_xor: bytes, new_hex: str) -> bytes:
    new_bytes = bytes.fromhex(new_hex)
    return bytes(a ^ b for a, b in zip(current_xor, new_bytes))

def sha256_file(path: str, bufsize: int = 1024 * 1024) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            b = f.read(bufsize)
            if not b:
                break
            h.update(b)
    return h.hexdigest()

# -----------------------------
# I/O
# -----------------------------

def iter_jsonl_gz(path: str) -> Iterator[Dict]:
    with gzip.open(path, "rt", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            yield json.loads(line)

def iter_jsonl(path: str) -> Iterator[Dict]:
    with open(path, "rt", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            yield json.loads(line)

def parse_bigint(x) -> int:
    if isinstance(x, int):
        return x
    if isinstance(x, str):
        return int(x)
    raise ValueError(f"Unsupported bigint type: {type(x)}")

# -----------------------------
# Config
# -----------------------------

@dataclass(frozen=True)
class Cfg:
    INIT_BITS: int
    MOD_BITS: int
    MAX_DEPTH: int
    BASIN_CUTOFF: int
    HASH_DIGEST_SIZE: int

def load_report(report_path: str) -> Dict:
    with open(report_path, "rt", encoding="utf-8") as f:
        return json.load(f)

def cfg_from_report(rep: Dict) -> Cfg:
    return Cfg(
        INIT_BITS=int(rep["INIT_BITS"]),
        MOD_BITS=int(rep["MOD_BITS"]),
        MAX_DEPTH=int(rep["MAX_DEPTH"]),
        BASIN_CUTOFF=int(rep["BASIN_CUTOFF"]),
        HASH_DIGEST_SIZE=int(rep.get("hash_digest_size", 32)),
    )

# -----------------------------
# prune_check semantics (must match generator)
# -----------------------------

def prune_check(a: int, t: int, b: int, basin_cutoff: int) -> bool:
    if a < 0 or t < 0:
        return False
    two_t = 1 << t
    A = pow(3, a)
    if two_t <= A:
        return False
    delta = two_t - A
    return b < basin_cutoff * delta

# -----------------------------
# Commitment over bucket witness record
# -----------------------------

def bucket_witness_canonical_bytes(w: Dict) -> bytes:
    n_mod = int(w["n_mod"])
    depth = int(w["depth"])
    a = int(w["a"])
    t = int(w["t"])
    b = str(w["b"])
    v2 = w.get("v2_last", None)
    v2s = str(v2 if v2 is not None else -1)
    fields = [
        ("kind", "bucket_prune"),
        ("n_mod", n_mod),
        ("depth", depth),
        ("a", a),
        ("t", t),
        ("b", b),
        ("v2_last", v2s),
    ]
    return "".join(f"{k}={v}\n" for k, v in fields).encode("ascii")

def bucket_witness_digest_hex(w: Dict, digest_size: int) -> str:
    h = blake2b(digest_size=digest_size)
    h.update(bucket_witness_canonical_bytes(w))
    return h.hexdigest()

# -----------------------------
# Key encoding: (depth, n_mod) -> uint64
# -----------------------------

U64 = struct.Struct("<Q")

def make_key_u64(depth: int, n_mod: int, mod_bits: int) -> int:
    # key = depth * 2^MOD_BITS + n_mod
    return (depth << mod_bits) | n_mod

def split_key_u64(key: int, mod_bits: int) -> Tuple[int, int]:
    depth = key >> mod_bits
    n_mod = key & ((1 << mod_bits) - 1)
    return depth, n_mod

# -----------------------------
# Disk-based key index build (cross-platform)
# -----------------------------

def build_key_chunks(bucket_gz: str, mod_bits: int, tmp_dir: str, chunk_keys: int) -> List[str]:
    """
    Stream bucket file, extract uint64 keys, sort in memory by chunks, write temp chunk files.
    Each chunk file is a raw little-endian uint64 stream.
    """
    os.makedirs(tmp_dir, exist_ok=True)
    chunk: List[int] = []
    chunk_files: List[str] = []
    n = 0
    t0 = time.time()

    def flush_chunk():
        nonlocal chunk, chunk_files
        if not chunk:
            return
        chunk.sort()
        fd, path = tempfile.mkstemp(prefix="bucket_keys_chunk_", suffix=".bin", dir=tmp_dir)
        os.close(fd)
        with open(path, "wb") as f:
            for k in chunk:
                f.write(U64.pack(k))
        chunk_files.append(path)
        chunk = []

    for w in iter_jsonl_gz(bucket_gz):
        depth = int(w["depth"])
        n_mod = int(w["n_mod"])
        k = make_key_u64(depth, n_mod, mod_bits)
        chunk.append(k)
        n += 1

        if len(chunk) >= chunk_keys:
            flush_chunk()

        if n % 5_000_000 == 0:
            dt = time.time() - t0
            print(f"[index] scanned={n:,} chunks={len(chunk_files)} elapsed={dt:.1f}s")

    flush_chunk()
    print(f"[index] done chunking: scanned={n:,} chunk_files={len(chunk_files)}")
    return chunk_files

def merge_chunks_to_sorted_uniq(chunk_files: List[str], out_path: str) -> Tuple[int, int]:
    """
    K-way merge sorted chunk files of uint64 keys into one sorted unique uint64 file.

    Returns:
      (total_keys_merged, unique_keys_written)
    """
    # Open all chunk streams
    fps = [open(p, "rb") for p in chunk_files]
    heap: List[Tuple[int, int]] = []  # (key, file_index)

    def read_u64(i: int) -> Optional[int]:
        b = fps[i].read(U64.size)
        if not b:
            return None
        return U64.unpack(b)[0]

    # init heap
    for i in range(len(fps)):
        k = read_u64(i)
        if k is not None:
            heappush(heap, (k, i))

    total = 0
    unique = 0
    last: Optional[int] = None

    with open(out_path, "wb") as out:
        while heap:
            k, i = heappop(heap)
            total += 1
            if last is None or k != last:
                out.write(U64.pack(k))
                unique += 1
                last = k
            nxt = read_u64(i)
            if nxt is not None:
                heappush(heap, (nxt, i))

    for f in fps:
        f.close()

    return total, unique

def build_key_index(bucket_gz: str, out_index: str, mod_bits: int, tmp_dir: str, chunk_keys: int, keep_chunks: bool) -> Dict:
    t0 = time.time()
    chunks = build_key_chunks(bucket_gz, mod_bits, tmp_dir, chunk_keys)
    total, unique = merge_chunks_to_sorted_uniq(chunks, out_index)
    dt = time.time() - t0

    if not keep_chunks:
        for p in chunks:
            try:
                os.remove(p)
            except OSError:
                pass

    return {
        "index_file": os.path.abspath(out_index),
        "index_sha256": sha256_file(out_index),
        "total_keys_merged": total,
        "unique_keys_written": unique,
        "elapsed_sec": dt,
    }

# -----------------------------
# Fast membership via mmap + binary search
# -----------------------------

def key_index_contains(mmv: mmap.mmap, key: int) -> bool:
    # file is packed uint64 LE, length multiple of 8
    n = mmv.size() // U64.size
    lo, hi = 0, n
    while lo < hi:
        mid = (lo + hi) // 2
        off = mid * U64.size
        cur = U64.unpack(mmv[off:off + U64.size])[0]
        if cur < key:
            lo = mid + 1
        else:
            hi = mid
    if lo >= n:
        return False
    off = lo * U64.size
    cur = U64.unpack(mmv[off:off + U64.size])[0]
    return cur == key

# -----------------------------
# Deterministic residue evolution (coverage walk)
# Matches generator's step_once for n_mod/depth updates.
# -----------------------------

def trailing_zeros_2(x: int) -> int:
    c = 0
    while (x & 1) == 0:
        x >>= 1
        c += 1
    return c

def next_residue(n_mod: int, mod_bits: int, mod_mask: int) -> int:
    if (n_mod & 1) == 0:
        return (n_mod >> 1) & mod_mask
    tmp = 3 * n_mod + 1
    tmp_masked = tmp & mod_mask
    if tmp_masked == 0:
        v_local = mod_bits
    else:
        v_local = trailing_zeros_2(tmp_masked)
    return (tmp_masked >> v_local) & mod_mask

def load_uncovered_seeds(uncovered_path: str) -> set:
    """
    Supports:
      - uncovered_*.jsonl(.gz): {"seed": <int>}
      - recheck_uncovered_witnesses.jsonl: {"seed": <int>, "witness": {...}}
    """
    seeds = set()
    if uncovered_path.endswith(".gz"):
        it = iter_jsonl_gz(uncovered_path)
    else:
        it = iter_jsonl(uncovered_path)
    for r in it:
        s = int(r["seed"])
        seeds.add(s)
    return seeds

def check_coverage(index_path: str,
                   uncovered_path: str,
                   init_bits: int,
                   mod_bits: int,
                   k_bound: int,
                   progress_every: int = 1_000_000) -> Dict:
    total_seeds = 1 << init_bits
    mod_mask = (1 << mod_bits) - 1

    uncovered = load_uncovered_seeds(uncovered_path)
    uncovered_count = len(uncovered)

    covered_by_bucket = 0
    failures = 0
    first_fail: Optional[int] = None

    with open(index_path, "rb") as f:
        mmv = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)

        t0 = time.time()
        for s in range(total_seeds):
            if s in uncovered:
                continue

            n_mod = s & mod_mask
            hit = False

            # check j = 0..k_bound
            # (depth=j, n_mod_j)
            for j in range(0, k_bound + 1):
                key = make_key_u64(j, n_mod, mod_bits)
                if key_index_contains(mmv, key):
                    hit = True
                    break
                # advance
                n_mod = next_residue(n_mod, mod_bits, mod_mask)

            if hit:
                covered_by_bucket += 1
            else:
                failures += 1
                if first_fail is None:
                    first_fail = s
                # fail fast: coverage is a theorem requirement
                break

            if (s + 1) % progress_every == 0:
                dt = time.time() - t0
                done = s + 1
                rate = done / max(dt, 1e-9)
                print(f"[coverage] done={done:,}/{total_seeds:,} "
                      f"covered_by_bucket={covered_by_bucket:,} "
                      f"uncovered={uncovered_count:,} "
                      f"rate={rate:,.0f} seeds/s")

        mmv.close()

    return {
        "coverage_ok": (failures == 0),
        "total_seeds": total_seeds,
        "uncovered_count": uncovered_count,
        "covered_by_bucket": covered_by_bucket,
        "failures": failures,
        "first_fail_seed": first_fail,
        "k_bound": k_bound,
        "index_file": os.path.abspath(index_path),
        "index_sha256": sha256_file(index_path),
        "uncovered_file": os.path.abspath(uncovered_path),
        "uncovered_sha256": sha256_file(uncovered_path),
    }

# -----------------------------
# Main acceptance + optional index + optional coverage
# -----------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True, help="run_INIT30_MOD40 directory")

    ap.add_argument("--report", default="report.json")
    ap.add_argument("--bucket", default="min_bucket_witnesses.jsonl.gz")
    ap.add_argument("--out", default="bucket_acceptance.json")

    # NEW: build key index
    ap.add_argument("--build-index", action="store_true", help="build sorted unique key index from bucket file")
    ap.add_argument("--index-file", default="bucket_keys_u64.sorted.uniq.bin", help="key index filename (in --dir)")
    ap.add_argument("--tmp-dir", default=None, help="temp dir for chunk files (default: <dir>/tmp_keys)")
    ap.add_argument("--chunk-keys", type=int, default=10_000_000,
                    help="keys per in-memory chunk (10M ~ 80MB). Reduce if low RAM.")
    ap.add_argument("--keep-chunks", action="store_true", help="do not delete temp chunk files")

    # NEW: coverage check
    ap.add_argument("--check-coverage", action="store_true", help="verify coverage for all seeds up to INIT_BITS")
    ap.add_argument("--k-bound", type=int, default=None, help="K bound; default uses report.MAX_DEPTH")
    ap.add_argument("--uncovered", default="recheck_uncovered_witnesses.jsonl",
                    help="uncovered seeds file (jsonl or jsonl.gz) in --dir")

    args = ap.parse_args()

    base = args.dir
    report_path = os.path.join(base, args.report)
    bucket_path = os.path.join(base, args.bucket)

    rep = load_report(report_path)
    cfg = cfg_from_report(rep)

    print("SHA256:")
    print("  bucket:", sha256_file(bucket_path))
    print("  report:", sha256_file(report_path))

    # -----------------------------
    # 1) Witness validity + commitments (existing behavior)
    # -----------------------------
    roll = ""
    x = bytes([0] * cfg.HASH_DIGEST_SIZE)
    checked = 0
    bad = 0

    for w in iter_jsonl_gz(bucket_path):
        checked += 1
        try:
            n_mod = int(w["n_mod"])
            depth = int(w["depth"])
            a = int(w["a"])
            t = int(w["t"])
            b = parse_bigint(w["b"])

            if not (0 <= n_mod < (1 << cfg.MOD_BITS)):
                raise ValueError("n_mod out of range")
            if not (0 <= depth <= cfg.MAX_DEPTH):
                raise ValueError("depth out of range")
            if not prune_check(a, t, b, cfg.BASIN_CUTOFF):
                raise ValueError("prune_check fails")

            dhex = bucket_witness_digest_hex(w, cfg.HASH_DIGEST_SIZE)
            roll = roll_hex_digest(roll, dhex, cfg.HASH_DIGEST_SIZE)
            x = xor_hex_digest(x, dhex)

        except Exception as e:
            bad += 1
            if bad <= 20:
                print(f"[BAD] #{checked} err={e} w={w}", file=sys.stderr)

        if checked % 1_000_000 == 0:
            print(f"[bucket] checked={checked:,} bad={bad:,} roll={(roll[:16]+'...') if roll else ''}")

    if bad != 0:
        raise SystemExit(f"FAILED: bad={bad}")

    out = {
        "accepted": True,
        "bucket_file": os.path.abspath(bucket_path),
        "bucket_sha256": sha256_file(bucket_path),
        "bucket_commit_roll": roll,
        "bucket_commit_xor": x.hex(),
        "digest_size": cfg.HASH_DIGEST_SIZE,
        "records_checked": checked,
        "params": {
            "INIT_BITS": cfg.INIT_BITS,
            "MOD_BITS": cfg.MOD_BITS,
            "MAX_DEPTH": cfg.MAX_DEPTH,
            "BASIN_CUTOFF": cfg.BASIN_CUTOFF,
        }
    }

    out_path = os.path.join(base, args.out)
    with open(out_path, "wt", encoding="utf-8") as f:
        json.dump(out, f, indent=2)
    print(f"\nOK(bucket). Wrote {out_path}")

    # -----------------------------
    # 2) Build index (optional)
    # -----------------------------
    index_info = None
    index_path = os.path.join(base, args.index_file)
    if args.build_index:
        tmp_dir = args.tmp_dir or os.path.join(base, "tmp_keys")
        print("\n[index] building key index (sorted unique uint64)...")
        index_info = build_key_index(
            bucket_gz=bucket_path,
            out_index=index_path,
            mod_bits=cfg.MOD_BITS,
            tmp_dir=tmp_dir,
            chunk_keys=args.chunk_keys,
            keep_chunks=args.keep_chunks,
        )
        print("[index] done:", index_info)

    # -----------------------------
    # 3) Coverage check (optional)
    # -----------------------------
    if args.check_coverage:
        uncovered_path = os.path.join(base, args.uncovered)
        if not os.path.exists(index_path):
            raise SystemExit(
                f"Coverage requires index file, not found: {index_path}\n"
                f"Run with --build-index first (or provide --index-file that exists)."
            )

        k_bound = args.k_bound
        if k_bound is None:
            # safest default: MAX_DEPTH from report
            k_bound = cfg.MAX_DEPTH

        print(f"\n[coverage] checking coverage for 2^{cfg.INIT_BITS} seeds with K={k_bound} ...")
        cov = check_coverage(
            index_path=index_path,
            uncovered_path=uncovered_path,
            init_bits=cfg.INIT_BITS,
            mod_bits=cfg.MOD_BITS,
            k_bound=k_bound,
        )

        cov_path = os.path.join(base, "coverage_report.json")
        with open(cov_path, "wt", encoding="utf-8") as f:
            json.dump(cov, f, indent=2)

        print("[coverage] wrote", cov_path)
        if not cov["coverage_ok"]:
            raise SystemExit(f"FAILED coverage: first_fail_seed={cov['first_fail_seed']}")

        print("[coverage] OK")

if __name__ == "__main__":
    main()
