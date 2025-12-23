#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
monster_collatz_search.py

Rewrites the generator to produce:

  1) min_bucket_witnesses.jsonl.gz
     - exactly ONE witness per (depth, n_mod) bucket (global, across all batches)
     - chosen as the "hardest" witness among batches for that same key

  2) bucket_keys_u64.sorted.uniq.bin
     - sorted unique uint64 keys for fast membership / coverage checks
     - key := (depth << MOD_BITS) | n_mod

  3) uncovered_seeds.jsonl.gz
     - all uncovered seeds (the ones that never hit prune_check by MAX_DEPTH)
     - one line per uncovered seed: {"seed": <int>}

  4) report.json
     - run parameters + global summary

Design notes:
- Per-batch we still run BFS search, but we write per-batch bucket witnesses as
  a *sorted* jsonl.gz stream (sorted by (depth, n_mod)).
- After all batches, we do a k-way merge over these sorted streams to build the
  global minimized witness set and key index in one pass, RAM-safe.
- Hardness tie-break uses (a, b, -t), because A=3^a is strictly monotone in a.
  This avoids recomputing huge A during merge.

This removes Coq-bucket emission entirely and produces audit-friendly artifacts
for the external checker.
"""

import argparse
import gzip
import hashlib
import json
import os
import struct
from collections import deque, defaultdict
from dataclasses import dataclass, asdict
from heapq import heappush, heappop
from typing import Optional, List, Dict, Tuple, Iterator, Any

# ============================================================
# 1) CONFIG
# ============================================================

@dataclass
class RunConfig:
    BASIN_CUTOFF: int
    MAX_DEPTH: int
    MOD_BITS: int
    INIT_BITS: int
    BATCH_SIZE: int
    OUTPUT_DIR: str

    # Output controls
    COMPRESS: bool  # gzip outputs
    MAX_QUEUE_STATES_SOFTCAP: int  # 0 disables

    # Hash/commitment controls (optional)
    WRITE_ROLL_XOR: bool
    HASH_DIGEST_SIZE: int

def make_default_config(out_dir: str) -> RunConfig:
    return RunConfig(
        BASIN_CUTOFF=1_000_000,
        MAX_DEPTH=300,
        MOD_BITS=40,
        INIT_BITS=30,
        BATCH_SIZE=1_000_000,
        OUTPUT_DIR=out_dir,

        COMPRESS=True,
        MAX_QUEUE_STATES_SOFTCAP=0,

        WRITE_ROLL_XOR=True,
        HASH_DIGEST_SIZE=32,
    )

# ============================================================
# 2) CORE MATH (same semantics as your original)
# ============================================================

def trailing_zeros_2(x: int) -> int:
    c = 0
    while (x & 1) == 0:
        x >>= 1
        c += 1
    return c

@dataclass
class State:
    a: int
    t: int
    A: int
    b: int
    n_mod: int
    depth: int
    v2_last: Optional[int]
    seed: int

def prune_check(st: State, cfg: RunConfig) -> bool:
    two_t = 1 << st.t
    if two_t <= st.A:
        return False
    delta = two_t - st.A
    return st.b < cfg.BASIN_CUTOFF * delta

def step_once(st: State, cfg: RunConfig, mod_mask: int) -> State:
    n_mod = st.n_mod

    # even
    if (n_mod & 1) == 0:
        return State(
            a=st.a,
            t=st.t + 1,
            A=st.A,
            b=st.b,
            n_mod=(n_mod >> 1) & mod_mask,
            depth=st.depth + 1,
            v2_last=None,
            seed=st.seed,
        )

    # odd
    tmp = 3 * n_mod + 1
    tmp_masked = tmp & mod_mask
    if tmp_masked == 0:
        v_local = cfg.MOD_BITS
    else:
        v_local = trailing_zeros_2(tmp_masked)

    return State(
        a=st.a + 1,
        t=st.t + v_local,
        A=st.A * 3,
        b=3 * st.b + (1 << st.t),
        n_mod=(tmp_masked >> v_local) & mod_mask,
        depth=st.depth + 1,
        v2_last=v_local,
        seed=st.seed,
    )

def dominates(hard: State, soft: State) -> bool:
    cond = (hard.A >= soft.A) and (hard.t <= soft.t) and (hard.b >= soft.b)
    strict = (hard.A > soft.A) or (hard.t < soft.t) or (hard.b > soft.b)
    return cond and strict

def hardness_key_state(st: State) -> Tuple[int, int, int]:
    # A=3^a monotone => compare by a instead of A to avoid huge ints in merge logic
    return (st.a, st.b, -st.t)

def harder_state(a: State, b: State) -> bool:
    return hardness_key_state(a) > hardness_key_state(b)

# ============================================================
# 3) COMMITMENTS (optional, for audit)
# ============================================================

def blake2b(digest_size: int) -> "hashlib._Hash":
    return hashlib.blake2b(digest_size=digest_size)

def roll_hex_digest(current_roll_hex: str, new_hex: str, digest_size: int) -> str:
    h = blake2b(digest_size=digest_size)
    if current_roll_hex:
        h.update(bytes.fromhex(current_roll_hex))
    h.update(bytes.fromhex(new_hex))
    return h.hexdigest()

def xor_hex_digest(current_xor: bytes, new_hex: str) -> bytes:
    nb = bytes.fromhex(new_hex)
    return bytes(a ^ b for a, b in zip(current_xor, nb))

def witness_canonical_bytes(st: State) -> bytes:
    # This matches the *bucket witness* semantics (not per-seed "prune" witness).
    # Keep stable field order.
    fields = [
        ("kind", "bucket_prune"),
        ("n_mod", st.n_mod),
        ("depth", st.depth),
        ("a", st.a),
        ("t", st.t),
        ("b", str(st.b)),
        ("v2_last", str(st.v2_last if st.v2_last is not None else -1)),
    ]
    return "".join(f"{k}={v}\n" for k, v in fields).encode("ascii")

def bucket_witness_digest_hex(st: State, digest_size: int) -> str:
    h = blake2b(digest_size=digest_size)
    h.update(witness_canonical_bytes(st))
    return h.hexdigest()

def sha256_file(path: str, bufsize: int = 1024 * 1024) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            b = f.read(bufsize)
            if not b:
                break
            h.update(b)
    return h.hexdigest()

# ============================================================
# 4) PER-BATCH SEARCH
# ============================================================

@dataclass
class BatchResult:
    monster_found: bool
    batch_max_depth: int
    max_v2_seen: int
    covered_count: int
    uncovered_seeds: List[int]
    # Sorted list of ((depth, n_mod), State) in key order
    bucket_items_sorted: List[Tuple[Tuple[int, int], State]]
    # Optional per-batch commitments over bucket items
    batch_roll: str
    batch_xor: str

def run_batch(cfg: RunConfig, seed_start: int, seed_end: int) -> BatchResult:
    MOD_MASK = (1 << cfg.MOD_BITS) - 1
    batch_size = seed_end - seed_start

    covered = bytearray(batch_size)
    covered_count = 0

    q = deque()
    frontier: Dict[Tuple[int, int], List[State]] = defaultdict(list)

    batch_max_depth = 0
    max_v2 = 0

    # hardest prune witness per (n_mod, depth)
    bucket_prune_witness: Dict[Tuple[int, int], State] = {}

    for seed in range(seed_start, seed_end):
        st0 = State(
            a=0, t=0, A=1, b=0,
            n_mod=seed & MOD_MASK,
            depth=0,
            v2_last=None,
            seed=seed,
        )
        q.append(st0)
        frontier[(st0.n_mod, 0)].append(st0)

    while q:
        if cfg.MAX_QUEUE_STATES_SOFTCAP and len(q) > cfg.MAX_QUEUE_STATES_SOFTCAP:
            raise MemoryError(f"Queue exceeded soft cap {cfg.MAX_QUEUE_STATES_SOFTCAP}.")

        st = q.popleft()
        batch_max_depth = max(batch_max_depth, st.depth)

        idx = st.seed - seed_start
        if covered[idx]:
            continue

        if st.depth >= cfg.MAX_DEPTH:
            # monster: seed(s) not covered within MAX_DEPTH
            uncovered_seeds = [seed_start + i for i in range(batch_size) if not covered[i]]
            items = sorted(bucket_prune_witness.items(), key=lambda kv: (kv[0][1], kv[0][0]))
            return BatchResult(
                monster_found=True,
                batch_max_depth=batch_max_depth,
                max_v2_seen=max_v2,
                covered_count=covered_count,
                uncovered_seeds=uncovered_seeds,
                bucket_items_sorted=items,
                batch_roll="",
                batch_xor="",
            )

        if prune_check(st, cfg):
            covered[idx] = 1
            covered_count += 1

            key = (st.n_mod, st.depth)
            prev = bucket_prune_witness.get(key)
            if prev is None or harder_state(st, prev):
                bucket_prune_witness[key] = st
            continue

        nxt = step_once(st, cfg, MOD_MASK)
        if nxt.v2_last is not None:
            max_v2 = max(max_v2, nxt.v2_last)

        key = (nxt.n_mod, nxt.depth)
        bucket = frontier[key]

        if any(dominates(old, nxt) for old in bucket):
            continue

        frontier[key] = [old for old in bucket if not dominates(nxt, old)] + [nxt]
        q.append(nxt)

    uncovered_seeds = [seed_start + i for i in range(batch_size) if not covered[i]]
    items = sorted(bucket_prune_witness.items(), key=lambda kv: (kv[0][1], kv[0][0]))  # (depth, n_mod)

    # Per-batch roll/xor over bucket witnesses (optional)
    batch_roll = ""
    batch_xor = bytes([0] * cfg.HASH_DIGEST_SIZE)
    if cfg.WRITE_ROLL_XOR:
        for (_k, st) in items:
            dhex = bucket_witness_digest_hex(st, cfg.HASH_DIGEST_SIZE)
            batch_roll = roll_hex_digest(batch_roll, dhex, cfg.HASH_DIGEST_SIZE)
            batch_xor = xor_hex_digest(batch_xor, dhex)

    return BatchResult(
        monster_found=False,
        batch_max_depth=batch_max_depth,
        max_v2_seen=max_v2,
        covered_count=covered_count,
        uncovered_seeds=uncovered_seeds,
        bucket_items_sorted=items,
        batch_roll=batch_roll,
        batch_xor=batch_xor.hex(),
    )

# ============================================================
# 5) PER-BATCH WRITERS
# ============================================================

def open_gz_or_text(path: str, compress: bool, mode: str):
    if compress:
        return gzip.open(path, mode, encoding="utf-8")
    return open(path, mode, encoding="utf-8")

def write_uncovered_append(path: str, seeds: List[int], compress: bool) -> None:
    # append mode
    mode = "at"
    with open_gz_or_text(path, compress, mode) as f:
        for s in seeds:
            f.write(json.dumps({"seed": s}) + "\n")

def write_bucket_batch(path: str, items_sorted: List[Tuple[Tuple[int, int], State]], compress: bool) -> int:
    """
    Writes sorted jsonl(.gz) where each record has ONLY bucket fields:
      {n_mod, depth, a, t, b, v2_last}
    Records are written in (depth, n_mod) order, which is also increasing key order.
    """
    with open_gz_or_text(path, compress, "wt") as f:
        for (n_mod, depth), st in items_sorted:
            rec = {
                "n_mod": int(n_mod),
                "depth": int(depth),
                "a": int(st.a),
                "t": int(st.t),
                "b": str(st.b),  # safe for huge ints
                "v2_last": None if st.v2_last is None else int(st.v2_last),
            }
            f.write(json.dumps(rec, separators=(",", ":")) + "\n")
    return len(items_sorted)

# ============================================================
# 6) GLOBAL MINIMIZATION: K-way merge of per-batch sorted streams
# ============================================================

U64 = struct.Struct("<Q")

def make_key_u64(depth: int, n_mod: int, mod_bits: int) -> int:
    return (depth << mod_bits) | n_mod

def iter_jsonl_gz(path: str) -> Iterator[Dict[str, Any]]:
    with gzip.open(path, "rt", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            yield json.loads(line)

def hardness_key_record(rec: Dict[str, Any]) -> Tuple[int, int, int]:
    # same idea as State: (a, b, -t)
    a = int(rec["a"])
    t = int(rec["t"])
    b = int(rec["b"])  # rec["b"] is string
    return (a, b, -t)

def kway_merge_minimize(batch_paths: List[str], out_min_bucket_gz: str, out_keys_bin: str, mod_bits: int, digest_size: int) -> Dict[str, Any]:
    """
    Merge all per-batch sorted streams (sorted by (depth, n_mod)).
    For each key=(depth,n_mod), keep the hardest record.
    Write:
      - min_bucket_witnesses.jsonl.gz (records in key-sorted order)
      - bucket_keys_u64.sorted.uniq.bin (keys in the same order)
    Also compute roll/xor commitments over the final minimized bucket list.
    """
    # open iterators
    iters = [iter_jsonl_gz(p) for p in batch_paths]

    # heap items: (key_u64, depth, n_mod, i, rec)
    heap: List[Tuple[int, int, int, int, Dict[str, Any]]] = []

    def push_next(i: int):
        try:
            rec = next(iters[i])
        except StopIteration:
            return
        depth = int(rec["depth"])
        n_mod = int(rec["n_mod"])
        key = make_key_u64(depth, n_mod, mod_bits)
        heappush(heap, (key, depth, n_mod, i, rec))

    for i in range(len(iters)):
        push_next(i)

    # outputs
    roll = ""
    x = bytes([0] * digest_size)

    written = 0
    keys_written = 0

    # stream writers
    os.makedirs(os.path.dirname(out_min_bucket_gz), exist_ok=True)
    with gzip.open(out_min_bucket_gz, "wt", encoding="utf-8") as fout, open(out_keys_bin, "wb") as fkeys:
        last_key: Optional[int] = None
        best_rec: Optional[Dict[str, Any]] = None

        while heap:
            key, depth, n_mod, i, rec = heappop(heap)

            # advance that iterator
            push_next(i)

            if last_key is None:
                last_key = key
                best_rec = rec
                continue

            if key == last_key:
                # choose hardest among duplicates for same key
                assert best_rec is not None
                if hardness_key_record(rec) > hardness_key_record(best_rec):
                    best_rec = rec
                continue

            # flush previous key
            assert best_rec is not None
            fout.write(json.dumps(best_rec, separators=(",", ":")) + "\n")
            fkeys.write(U64.pack(last_key))
            written += 1
            keys_written += 1

            # commitment over *final* minimized bucket witness record
            # (same canonicalization as checker)
            # Rebuild a minimal canonical structure and hash it.
            tmp = {
                "n_mod": int(best_rec["n_mod"]),
                "depth": int(best_rec["depth"]),
                "a": int(best_rec["a"]),
                "t": int(best_rec["t"]),
                "b": str(best_rec["b"]),
                "v2_last": best_rec.get("v2_last", None),
            }
            # canonicalize exactly like earlier
            v2 = tmp.get("v2_last", None)
            v2s = str(v2 if v2 is not None else -1)
            canon = (
                f"kind=bucket_prune\n"
                f"n_mod={tmp['n_mod']}\n"
                f"depth={tmp['depth']}\n"
                f"a={tmp['a']}\n"
                f"t={tmp['t']}\n"
                f"b={tmp['b']}\n"
                f"v2_last={v2s}\n"
            ).encode("ascii")
            h = blake2b(digest_size=digest_size)
            h.update(canon)
            dhex = h.hexdigest()
            roll = roll_hex_digest(roll, dhex, digest_size)
            x = xor_hex_digest(x, dhex)

            # start new group
            last_key = key
            best_rec = rec

        # flush final group
        if last_key is not None and best_rec is not None:
            fout.write(json.dumps(best_rec, separators=(",", ":")) + "\n")
            fkeys.write(U64.pack(last_key))
            written += 1
            keys_written += 1

            v2 = best_rec.get("v2_last", None)
            v2s = str(v2 if v2 is not None else -1)
            canon = (
                f"kind=bucket_prune\n"
                f"n_mod={int(best_rec['n_mod'])}\n"
                f"depth={int(best_rec['depth'])}\n"
                f"a={int(best_rec['a'])}\n"
                f"t={int(best_rec['t'])}\n"
                f"b={str(best_rec['b'])}\n"
                f"v2_last={v2s}\n"
            ).encode("ascii")
            h = blake2b(digest_size=digest_size)
            h.update(canon)
            dhex = h.hexdigest()
            roll = roll_hex_digest(roll, dhex, digest_size)
            x = xor_hex_digest(x, dhex)

    return {
        "min_bucket_records": written,
        "keys_written": keys_written,
        "bucket_commit_roll": roll,
        "bucket_commit_xor": x.hex(),
    }

# ============================================================
# 7) DRIVER
# ============================================================

def driver(cfg: RunConfig) -> None:
    os.makedirs(cfg.OUTPUT_DIR, exist_ok=True)

    # Persist config
    with open(os.path.join(cfg.OUTPUT_DIR, "config.json"), "w", encoding="utf-8") as f:
        json.dump(asdict(cfg), f, indent=2)

    INIT_MOD = 1 << cfg.INIT_BITS
    total_batches = (INIT_MOD + cfg.BATCH_SIZE - 1) // cfg.BATCH_SIZE

    uncovered_path = os.path.join(cfg.OUTPUT_DIR, "uncovered_seeds.jsonl.gz" if cfg.COMPRESS else "uncovered_seeds.jsonl")
    # reset uncovered file
    if os.path.exists(uncovered_path):
        os.remove(uncovered_path)

    batch_paths: List[str] = []

    any_monster = False
    global_best_depth = -1
    global_max_v2 = 0
    global_uncovered = 0

    summaries: List[Dict[str, Any]] = []

    print(f"INIT_BITS={cfg.INIT_BITS} => {INIT_MOD} residues total.")
    print(f"Processing in {total_batches} batches of size {cfg.BATCH_SIZE}.\n")

    for batch_i, start in enumerate(range(0, INIT_MOD, cfg.BATCH_SIZE), start=1):
        end = min(start + cfg.BATCH_SIZE, INIT_MOD)
        print(f"=== BATCH {batch_i}/{total_batches} [{start}:{end}) ===")

        res = run_batch(cfg, start, end)

        any_monster |= res.monster_found
        global_best_depth = max(global_best_depth, res.batch_max_depth)
        global_max_v2 = max(global_max_v2, res.max_v2_seen)
        global_uncovered += len(res.uncovered_seeds)

        # append uncovered
        write_uncovered_append(uncovered_path, res.uncovered_seeds, compress=cfg.COMPRESS)

        # write per-batch bucket witness list (sorted)
        batch_bucket_name = f"bucket_batch_{start}_{end}.jsonl.gz" if cfg.COMPRESS else f"bucket_batch_{start}_{end}.jsonl"
        batch_bucket_path = os.path.join(cfg.OUTPUT_DIR, batch_bucket_name)
        n_written = write_bucket_batch(batch_bucket_path, res.bucket_items_sorted, compress=cfg.COMPRESS)
        batch_paths.append(batch_bucket_path)

        summaries.append({
            "batch": [start, end],
            "monster_found": res.monster_found,
            "batch_max_depth": res.batch_max_depth,
            "max_v2_seen": res.max_v2_seen,
            "covered_count": res.covered_count,
            "uncovered_count": len(res.uncovered_seeds),
            "bucket_witness_count": n_written,
            "bucket_batch_file": batch_bucket_name,
            "batch_commit_roll": res.batch_roll if cfg.WRITE_ROLL_XOR else None,
            "batch_commit_xor": res.batch_xor if cfg.WRITE_ROLL_XOR else None,
        })

        print(f"Batch done: monster={res.monster_found} max_depth={res.batch_max_depth} "
              f"covered={res.covered_count}/{end-start} uncovered={len(res.uncovered_seeds)} "
              f"bucket_witnesses={n_written}")
        if cfg.WRITE_ROLL_XOR:
            print(f"  batch_commit_roll={res.batch_roll}")
            print(f"  batch_commit_xor ={res.batch_xor}")
        print(f"  uncovered_append_file={os.path.basename(uncovered_path)}")
        print(f"  bucket_batch_file    ={batch_bucket_name}")
        print()

        if res.monster_found:
            break

    # batch summaries
    with open(os.path.join(cfg.OUTPUT_DIR, "batch_summaries.jsonl"), "w", encoding="utf-8") as f:
        for s in summaries:
            f.write(json.dumps(s) + "\n")

    # minimize globally (k-way merge)
    min_bucket_path = os.path.join(cfg.OUTPUT_DIR, "min_bucket_witnesses.jsonl.gz")
    keys_bin_path = os.path.join(cfg.OUTPUT_DIR, "bucket_keys_u64.sorted.uniq.bin")

    print("=== GLOBAL MINIMIZATION (k-way merge) ===")
    merge_info = kway_merge_minimize(
        batch_paths=batch_paths,
        out_min_bucket_gz=min_bucket_path,
        out_keys_bin=keys_bin_path,
        mod_bits=cfg.MOD_BITS,
        digest_size=cfg.HASH_DIGEST_SIZE,
    )
    print("Minimized bucket written:", os.path.basename(min_bucket_path))
    print("Key index written       :", os.path.basename(keys_bin_path))
    print("min_bucket_records      :", merge_info["min_bucket_records"])
    print("bucket_commit_roll      :", merge_info["bucket_commit_roll"])
    print("bucket_commit_xor       :", merge_info["bucket_commit_xor"])
    print()

    # final report
    report = {
        "INIT_BITS": cfg.INIT_BITS,
        "MOD_BITS": cfg.MOD_BITS,
        "MAX_DEPTH": cfg.MAX_DEPTH,
        "BASIN_CUTOFF": cfg.BASIN_CUTOFF,
        "BATCH_SIZE": cfg.BATCH_SIZE,
        "any_monster": any_monster,
        "deepest_depth_overall": global_best_depth,
        "global_max_v2": global_max_v2,
        "global_uncovered": global_uncovered,
        "hash_algo": "blake2b" if cfg.WRITE_ROLL_XOR else None,
        "hash_digest_size": cfg.HASH_DIGEST_SIZE if cfg.WRITE_ROLL_XOR else None,
        "outputs": {
            "uncovered_seeds": os.path.basename(uncovered_path),
            "min_bucket_witnesses": os.path.basename(min_bucket_path),
            "bucket_keys_index": os.path.basename(keys_bin_path),
        },
        "min_bucket_acceptance": {
            "bucket_sha256": sha256_file(min_bucket_path),
            "index_sha256": sha256_file(keys_bin_path),
            "bucket_commit_roll": merge_info["bucket_commit_roll"],
            "bucket_commit_xor": merge_info["bucket_commit_xor"],
            "min_bucket_records": merge_info["min_bucket_records"],
        }
    }

    with open(os.path.join(cfg.OUTPUT_DIR, "report.json"), "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2)

    print("=== DONE ===")
    print("Wrote:")
    print(" - config.json")
    print(" - batch_summaries.jsonl")
    print(f" - {os.path.basename(uncovered_path)}")
    print(" - per-batch bucket_batch_START_END.jsonl(.gz)")
    print(" - min_bucket_witnesses.jsonl.gz")
    print(" - bucket_keys_u64.sorted.uniq.bin")
    print(" - report.json")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="run_INIT30_MOD40_minimized", help="output directory")
    ap.add_argument("--batch-size", type=int, default=1_000_000)
    ap.add_argument("--init-bits", type=int, default=30)
    ap.add_argument("--mod-bits", type=int, default=40)
    ap.add_argument("--max-depth", type=int, default=300)
    ap.add_argument("--basin-cutoff", type=int, default=1_000_000)
    ap.add_argument("--no-gzip", action="store_true")
    ap.add_argument("--no-commitments", action="store_true")
    ap.add_argument("--queue-softcap", type=int, default=0)
    args = ap.parse_args()

    cfg = make_default_config(args.out)
    cfg.BATCH_SIZE = args.batch_size
    cfg.INIT_BITS = args.init_bits
    cfg.MOD_BITS = args.mod_bits
    cfg.MAX_DEPTH = args.max_depth
    cfg.BASIN_CUTOFF = args.basin_cutoff
    cfg.COMPRESS = (not args.no_gzip)
    cfg.WRITE_ROLL_XOR = (not args.no_commitments)
    cfg.MAX_QUEUE_STATES_SOFTCAP = args.queue_softcap

    driver(cfg)

if __name__ == "__main__":
    main()
