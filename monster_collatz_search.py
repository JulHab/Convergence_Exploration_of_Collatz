#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import json
import os
import gzip
import hashlib
from collections import deque, defaultdict
from dataclasses import dataclass, asdict
from typing import Optional, List, Dict, Tuple

# ============================================================
# 1. CONFIG
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
    WRITE_UNCOVERED: bool
    UNCOVERED_COMPRESS: bool
    UNCOVERED_MAX_WRITE: int     # cap how many uncovered seeds to write per batch (0 = no cap)

    # Safety valve
    MAX_QUEUE_STATES_SOFTCAP: int  # 0 disables

    # Hash/commitment controls
    WRITE_HASHES: bool
    HASH_DIGEST_SIZE: int          # bytes, e.g. 32 = 256-bit
    HASH_ORDER_INDEPENDENT: bool   # also compute XOR commitment if True
    HASH_INCLUDE_A: bool           # include A in witness hash payload (recommended True if you store/compute it)

    # Coq proof-log output (bucket witnesses)
    WRITE_COQ_BUCKETS: bool
    COQ_BUCKETS_PER_BATCH: bool
    COQ_WRITE_GLUE_FILE: bool
    COQ_MODULE_PREFIX: str
    COQ_BUCKET_TYPE: str           # Coq type name, e.g. "BucketCertificate"


def make_default_config() -> RunConfig:
    return RunConfig(
        BASIN_CUTOFF=1_000_000,
        MAX_DEPTH=300,
        MOD_BITS=40,
        INIT_BITS=30,
        BATCH_SIZE=1_000_000,
        OUTPUT_DIR="run_INIT30_MOD40",

        WRITE_UNCOVERED=True,
        UNCOVERED_COMPRESS=True,
        UNCOVERED_MAX_WRITE=0,        # 0 = unlimited

        MAX_QUEUE_STATES_SOFTCAP=0,   # set e.g. 25_000_000 if you want a cap

        WRITE_HASHES=True,
        HASH_DIGEST_SIZE=32,
        HASH_ORDER_INDEPENDENT=True,
        HASH_INCLUDE_A=True,

        WRITE_COQ_BUCKETS=True,
        COQ_BUCKETS_PER_BATCH=True,
        COQ_WRITE_GLUE_FILE=True,
        COQ_MODULE_PREFIX="BucketWitnesses",
        COQ_BUCKET_TYPE="BucketCertificate",
    )

# ============================================================
# 2. CORE MATH
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
    seed: int  # absolute seed value


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


def hardness_key(st: State) -> Tuple[int, int, int]:
    """
    Larger = harder:
      - larger A is harder
      - larger b is harder
      - smaller t is harder  => use -t
    """
    return (st.A, st.b, -st.t)


def harder_than(a: State, b: State) -> bool:
    return hardness_key(a) > hardness_key(b)

# ============================================================
# 3. HASHING / COMMITMENTS
# ============================================================

def _blake2b(digest_size: int) -> "hashlib._Hash":
    return hashlib.blake2b(digest_size=digest_size)

def witness_canonical_bytes(seed: int, st: State, include_A: bool) -> bytes:
    fields = [
        ("seed", seed),
        ("kind", "prune"),
        ("j", st.depth),
        ("a", st.a),
        ("t", st.t),
        ("b", st.b),
        ("n_mod", st.n_mod),
        ("v2_last", st.v2_last if st.v2_last is not None else -1),
    ]
    if include_A:
        fields.append(("A", st.A))
    return "".join(f"{k}={v}\n" for k, v in fields).encode("ascii")

def witness_digest_hex(seed: int, st: State, cfg: RunConfig) -> str:
    h = _blake2b(cfg.HASH_DIGEST_SIZE)
    h.update(witness_canonical_bytes(seed, st, include_A=cfg.HASH_INCLUDE_A))
    return h.hexdigest()

def xor_hex_digest(current_xor: bytes, new_hex: str) -> bytes:
    new_bytes = bytes.fromhex(new_hex)
    return bytes(a ^ b for a, b in zip(current_xor, new_bytes))

def roll_hex_digest(current_roll_hex: str, new_hex: str, cfg: RunConfig) -> str:
    h = _blake2b(cfg.HASH_DIGEST_SIZE)
    if current_roll_hex:
        h.update(bytes.fromhex(current_roll_hex))
    h.update(bytes.fromhex(new_hex))
    return h.hexdigest()

# ============================================================
# 4. COQ EMITTER (Bucket certificates)
# ============================================================

def coq_z(n: int) -> str:
    return f"({n})%Z"

def coq_opt_z(v: Optional[int]) -> str:
    if v is None:
        return "None"
    return f"(Some {coq_z(v)})"

def coq_bucket_cert_record(key: Tuple[int, int], st: State) -> str:
    """
    IMPORTANT: adjust field names to match your Coq record later.
    For now we output a generic BucketCertificate record with:
      n_mod_c, depth_c, a_c, t_c, A_c, b_c, v2_last_c
    """
    n_mod, depth = key
    return (
        "{| "
        f"n_mod_c := {coq_z(n_mod)}; "
        f"depth_c := {coq_z(depth)}; "
        f"a_c := {coq_z(st.a)}; "
        f"t_c := {coq_z(st.t)}; "
        f"A_c := {coq_z(st.A)}; "
        f"b_c := {coq_z(st.b)}; "
        f"v2_last_c := {coq_opt_z(st.v2_last)} "
        "|}"
    )

def write_coq_bucket_file(path: str, def_name: str,
                          bucket_items: List[Tuple[Tuple[int, int], State]],
                          coq_type: str) -> None:
    with open(path, "w", encoding="utf-8") as f:
        f.write("From Coq Require Import ZArith List.\n")
        f.write("Import ListNotations.\n")
        f.write("Open Scope Z_scope.\n\n")
        f.write("(* Auto-generated bucket witnesses: one hardest-prune witness per (n_mod, depth). *)\n\n")
        f.write(f"Definition {def_name} : list {coq_type} :=\n")
        f.write("  [\n")
        for key, st in bucket_items:
            f.write("    " + coq_bucket_cert_record(key, st) + ";\n")
        f.write("  ].\n")

def write_coq_glue_file(path: str, coq_type: str, batch_defs: List[str], batch_modules: List[str]) -> None:
    with open(path, "w", encoding="utf-8") as f:
        f.write("From Coq Require Import List.\n")
        f.write("Import ListNotations.\n\n")
        f.write("(* Auto-generated glue file: concatenates per-batch bucket certificate lists. *)\n\n")
        for mod in batch_modules:
            f.write(f"Require Import {mod}.\n")
        f.write("\n")
        f.write(f"Definition collatz_bucket_certs : list {coq_type} :=\n  ")
        if not batch_defs:
            f.write("[] .\n")
            return
        f.write(" ++\n  ".join(batch_defs))
        f.write(".\n")

# ============================================================
# 5. I/O HELPERS
# ============================================================

def open_textmaybe_gzip(path: str, compress: bool):
    if compress:
        return gzip.open(path, "wt", encoding="utf-8")
    return open(path, "w", encoding="utf-8")

def write_uncovered_jsonl(path: str, seeds: List[int], compress: bool, max_write: int) -> int:
    if max_write and len(seeds) > max_write:
        seeds = seeds[:max_write]
    with open_textmaybe_gzip(path, compress) as f:
        for s in seeds:
            f.write(json.dumps({"seed": s}) + "\n")
    return len(seeds)

# ============================================================
# 6. BATCH SEARCH (bucket witnesses)
# ============================================================

@dataclass
class BatchResult:
    monster_found: bool
    batch_max_depth: int
    max_v2_seen: int

    covered_count: int
    uncovered_count: int
    uncovered_seeds: List[int]

    bucket_witnesses: List[Tuple[Tuple[int, int], State]]

    batch_hash_roll: str
    batch_hash_xor: str


def run_batch(cfg: RunConfig, seed_start: int, seed_end: int) -> BatchResult:
    MOD_MASK = (1 << cfg.MOD_BITS) - 1
    batch_size = seed_end - seed_start

    covered = bytearray(batch_size)
    covered_count = 0

    q = deque()
    frontier: Dict[Tuple[int, int], List[State]] = defaultdict(list)

    batch_max_depth = 0
    max_v2 = 0

    batch_roll = ""
    batch_xor = bytes([0] * cfg.HASH_DIGEST_SIZE)

    # Store hardest prune witness per bucket (n_mod, depth)
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
            uncovered_seeds = [seed_start + i for i in range(batch_size) if not covered[i]]
            return BatchResult(
                monster_found=True,
                batch_max_depth=batch_max_depth,
                max_v2_seen=max_v2,
                covered_count=covered_count,
                uncovered_count=len(uncovered_seeds),
                uncovered_seeds=uncovered_seeds,
                bucket_witnesses=sorted(bucket_prune_witness.items(),
                                       key=lambda kv: (kv[0][1], kv[0][0])),
                batch_hash_roll=batch_roll,
                batch_hash_xor=batch_xor.hex(),
            )

        if prune_check(st, cfg):
            covered[idx] = 1
            covered_count += 1

            key = (st.n_mod, st.depth)
            prev = bucket_prune_witness.get(key)
            if prev is None or harder_than(st, prev):
                bucket_prune_witness[key] = st

            # Hash as audit (still per-seed)
            if cfg.WRITE_HASHES:
                dhex = witness_digest_hex(st.seed, st, cfg)
                batch_roll = roll_hex_digest(batch_roll, dhex, cfg)
                if cfg.HASH_ORDER_INDEPENDENT:
                    batch_xor = xor_hex_digest(batch_xor, dhex)

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
    return BatchResult(
        monster_found=False,
        batch_max_depth=batch_max_depth,
        max_v2_seen=max_v2,
        covered_count=covered_count,
        uncovered_count=len(uncovered_seeds),
        uncovered_seeds=uncovered_seeds,
        bucket_witnesses=sorted(bucket_prune_witness.items(),
                               key=lambda kv: (kv[0][1], kv[0][0])),
        batch_hash_roll=batch_roll,
        batch_hash_xor=batch_xor.hex(),
    )

# ============================================================
# 7. DRIVER
# ============================================================

def driver():
    cfg = make_default_config()
    os.makedirs(cfg.OUTPUT_DIR, exist_ok=True)

    with open(os.path.join(cfg.OUTPUT_DIR, "config.json"), "w", encoding="utf-8") as f:
        json.dump(asdict(cfg), f, indent=2)

    INIT_MOD = 1 << cfg.INIT_BITS
    total_batches = (INIT_MOD + cfg.BATCH_SIZE - 1) // cfg.BATCH_SIZE

    print(f"INIT_BITS={cfg.INIT_BITS} => {INIT_MOD} residues total.")
    print(f"Processing in {total_batches} batches of size {cfg.BATCH_SIZE}.\n")

    summaries: List[Dict] = []
    any_monster = False
    global_best_depth = -1
    global_max_v2 = 0
    global_uncovered = 0

    global_roll = ""
    global_xor = bytes([0] * cfg.HASH_DIGEST_SIZE)

    batch_def_names: List[str] = []
    batch_module_names: List[str] = []

    for batch_i, start in enumerate(range(0, INIT_MOD, cfg.BATCH_SIZE), start=1):
        end = min(start + cfg.BATCH_SIZE, INIT_MOD)
        print(f"=== BATCH {batch_i}/{total_batches} [{start}:{end}) ===")

        res = run_batch(cfg, start, end)

        any_monster |= res.monster_found
        global_best_depth = max(global_best_depth, res.batch_max_depth)
        global_max_v2 = max(global_max_v2, res.max_v2_seen)
        global_uncovered += res.uncovered_count

        # uncovered output
        unc_path_base = os.path.join(cfg.OUTPUT_DIR, f"uncovered_{start}_{end}.jsonl")
        unc_path = unc_path_base + (".gz" if cfg.UNCOVERED_COMPRESS else "")
        written = 0
        truncated = False
        if cfg.WRITE_UNCOVERED:
            written = write_uncovered_jsonl(
                unc_path,
                res.uncovered_seeds,
                compress=cfg.UNCOVERED_COMPRESS,
                max_write=cfg.UNCOVERED_MAX_WRITE,
            )
            truncated = bool(cfg.UNCOVERED_MAX_WRITE and (written < res.uncovered_count))

        # Coq bucket certs output
        coq_path = None
        coq_def_name = None
        if cfg.WRITE_COQ_BUCKETS and cfg.COQ_BUCKETS_PER_BATCH:
            coq_def_name = f"bucket_witnesses_{start}_{end}"
            coq_filename = f"{cfg.COQ_MODULE_PREFIX}_{start}_{end}.v"
            coq_path = os.path.join(cfg.OUTPUT_DIR, coq_filename)
            write_coq_bucket_file(coq_path, coq_def_name, res.bucket_witnesses, cfg.COQ_BUCKET_TYPE)

            batch_def_names.append(coq_def_name)
            batch_module_names.append(os.path.splitext(coq_filename)[0])

        # update global commitments
        if cfg.WRITE_HASHES and res.batch_hash_roll:
            global_roll = roll_hex_digest(global_roll, res.batch_hash_roll, cfg)
            if cfg.HASH_ORDER_INDEPENDENT and res.batch_hash_xor:
                global_xor = xor_hex_digest(global_xor, res.batch_hash_xor)

        summaries.append({
            "batch": [start, end],
            "monster_found": res.monster_found,
            "batch_max_depth": res.batch_max_depth,
            "max_v2_seen": res.max_v2_seen,
            "covered_count": res.covered_count,
            "uncovered_count": res.uncovered_count,
            "uncovered_path": unc_path if cfg.WRITE_UNCOVERED else None,
            "uncovered_written": written if cfg.WRITE_UNCOVERED else 0,
            "uncovered_truncated": truncated,
            "bucket_witness_count": len(res.bucket_witnesses),
            "coq_bucket_file": coq_path,
            "coq_bucket_def": coq_def_name,
            "batch_hash_roll": res.batch_hash_roll if cfg.WRITE_HASHES else None,
            "batch_hash_xor": res.batch_hash_xor if (cfg.WRITE_HASHES and cfg.HASH_ORDER_INDEPENDENT) else None,
        })

        print(f"Batch done: monster={res.monster_found} max_depth={res.batch_max_depth} "
              f"covered={res.covered_count}/{end-start} uncovered={res.uncovered_count} "
              f"bucket_witnesses={len(res.bucket_witnesses)}")
        if cfg.WRITE_HASHES:
            print(f"  batch_hash_roll={res.batch_hash_roll}")
            if cfg.HASH_ORDER_INDEPENDENT:
                print(f"  batch_hash_xor ={res.batch_hash_xor}")
        if cfg.WRITE_UNCOVERED:
            print(f"  uncovered_file={unc_path} (written={written}, truncated={truncated})")
        if cfg.WRITE_COQ_BUCKETS and cfg.COQ_BUCKETS_PER_BATCH:
            print(f"  coq_bucket_file={coq_path} (def {coq_def_name})")
        print()

        if res.monster_found:
            break

    # summaries
    with open(os.path.join(cfg.OUTPUT_DIR, "batch_summaries.jsonl"), "w", encoding="utf-8") as f:
        for s in summaries:
            f.write(json.dumps(s) + "\n")

    # glue file
    if cfg.WRITE_COQ_BUCKETS and cfg.COQ_WRITE_GLUE_FILE and batch_def_names:
        glue_path = os.path.join(cfg.OUTPUT_DIR, "BucketWitnesses_glue.v")
        write_coq_glue_file(glue_path, cfg.COQ_BUCKET_TYPE, batch_def_names, batch_module_names)
        print("Wrote Coq glue file:", glue_path)

    # report
    with open(os.path.join(cfg.OUTPUT_DIR, "report.json"), "w", encoding="utf-8") as f:
        json.dump({
            "INIT_BITS": cfg.INIT_BITS,
            "MOD_BITS": cfg.MOD_BITS,
            "MAX_DEPTH": cfg.MAX_DEPTH,
            "BASIN_CUTOFF": cfg.BASIN_CUTOFF,
            "BATCH_SIZE": cfg.BATCH_SIZE,
            "any_monster": any_monster,
            "deepest_depth_overall": global_best_depth,
            "global_max_v2": global_max_v2,
            "global_uncovered": global_uncovered,
            "global_hash_roll": global_roll if cfg.WRITE_HASHES else None,
            "global_hash_xor": global_xor.hex() if (cfg.WRITE_HASHES and cfg.HASH_ORDER_INDEPENDENT) else None,
            "hash_algo": "blake2b" if cfg.WRITE_HASHES else None,
            "hash_digest_size": cfg.HASH_DIGEST_SIZE if cfg.WRITE_HASHES else None,
            "hash_include_A": cfg.HASH_INCLUDE_A if cfg.WRITE_HASHES else None,
            "coq_bucket_written": bool(cfg.WRITE_COQ_BUCKETS),
            "coq_bucket_per_batch": bool(cfg.COQ_BUCKETS_PER_BATCH),
            "coq_bucket_glue_written": bool(cfg.COQ_WRITE_GLUE_FILE and batch_def_names),
        }, f, indent=2)

    print("=== GLOBAL SUMMARY ===")
    print("any_monster:", any_monster)
    print("deepest_depth_overall:", global_best_depth)
    print("global_max_v2:", global_max_v2)
    print("global_uncovered:", global_uncovered)
    if cfg.WRITE_HASHES:
        print("global_hash_roll:", global_roll)
        if cfg.HASH_ORDER_INDEPENDENT:
            print("global_hash_xor :", global_xor.hex())
    print("Wrote:")
    print(" - config.json")
    print(" - batch_summaries.jsonl")
    print(" - uncovered_START_END.jsonl(.gz) per batch")
    print(" - report.json")
    if cfg.WRITE_COQ_BUCKETS and cfg.COQ_BUCKETS_PER_BATCH:
        print(f" - {cfg.COQ_MODULE_PREFIX}_START_END.v per batch (BucketCertificate lists)")
    if cfg.WRITE_COQ_BUCKETS and cfg.COQ_WRITE_GLUE_FILE:
        print(" - BucketWitnesses_glue.v")


if __name__ == "__main__":
    driver()
