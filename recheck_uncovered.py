#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import json
import gzip
from dataclasses import dataclass
from typing import Optional, Dict, List, Tuple
from collections import deque

# -----------------------------
# Config I/O
# -----------------------------

@dataclass
class RunCfg:
    BASIN_CUTOFF: int
    MAX_DEPTH: int
    MOD_BITS: int

def load_cfg(run_dir: str) -> RunCfg:
    p = os.path.join(run_dir, "config.json")
    with open(p, "r", encoding="utf-8") as f:
        d = json.load(f)
    return RunCfg(
        BASIN_CUTOFF=int(d["BASIN_CUTOFF"]),
        MAX_DEPTH=int(d["MAX_DEPTH"]),
        MOD_BITS=int(d["MOD_BITS"]),
    )

# -----------------------------
# Core model (same as your search)
# -----------------------------

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

def prune_check(st: State, cutoff: int) -> bool:
    two_t = 1 << st.t
    if two_t <= st.A:
        return False
    delta = two_t - st.A
    return st.b < cutoff * delta

def step_once(st: State, MOD_BITS: int, mod_mask: int) -> State:
    n_mod = st.n_mod

    if (n_mod & 1) == 0:
        return State(
            a=st.a,
            t=st.t + 1,
            A=st.A,
            b=st.b,
            n_mod=(n_mod >> 1) & mod_mask,
            depth=st.depth + 1,
            v2_last=None,
        )

    tmp = 3 * n_mod + 1
    tmp_masked = tmp & mod_mask
    if tmp_masked == 0:
        v_local = MOD_BITS
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
    )

def summarize(st: State) -> Dict[str, int]:
    return {
        "depth": st.depth,
        "a": st.a,
        "t": st.t,
        "A": st.A,
        "b": st.b,
        "n_mod": st.n_mod,
        "v2_last": st.v2_last if st.v2_last is not None else -1,
    }

# -----------------------------
# Uncovered input
# -----------------------------

def read_jsonl_maybe_gz(path: str) -> List[Dict]:
    if path.endswith(".gz"):
        opener = lambda p: gzip.open(p, "rt", encoding="utf-8")
    else:
        opener = lambda p: open(p, "r", encoding="utf-8")

    rows = []
    with opener(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            rows.append(json.loads(line))
    return rows

def find_uncovered_files(run_dir: str) -> List[str]:
    outs = []
    for fn in os.listdir(run_dir):
        if fn.startswith("uncovered_") and (fn.endswith(".jsonl") or fn.endswith(".jsonl.gz")):
            outs.append(os.path.join(run_dir, fn))
    return sorted(outs)

# -----------------------------
# Recheck logic: NO dominance pruning
# -----------------------------

def recheck_seed(seed: int, cfg: RunCfg) -> Tuple[bool, int, Optional[Dict[str, int]]]:
    """
    Returns:
      (is_monster, max_depth_reached, prune_witness_state_or_None)
    Search mode: breadth-first expansion of *single seed* without dominance pruning.
    Stop when prune_check triggers (witness found), OR when depth reaches MAX_DEPTH (monster).
    """
    MOD_MASK = (1 << cfg.MOD_BITS) - 1

    # We do not need a full BFS frontier structure; for single-seed,
    # a simple queue is fine. (Still deterministic.)
    q = deque()

    st0 = State(a=0, t=0, A=1, b=0, n_mod=seed & MOD_MASK, depth=0, v2_last=None)
    q.append(st0)

    max_depth = 0

    while q:
        st = q.popleft()
        if st.depth > max_depth:
            max_depth = st.depth

        if st.depth >= cfg.MAX_DEPTH:
            return True, max_depth, None  # monster for this seed

        if prune_check(st, cfg.BASIN_CUTOFF):
            return False, max_depth, summarize(st)

        nxt = step_once(st, cfg.MOD_BITS, MOD_MASK)
        q.append(nxt)

    # If queue exhausts (should not happen for this deterministic single path), treat as safe
    return False, max_depth, None

# -----------------------------
# Main
# -----------------------------

def main(run_dir: str):
    cfg = load_cfg(run_dir)
    unc_files = find_uncovered_files(run_dir)
    if not unc_files:
        print("No uncovered_*.jsonl(.gz) files found.")
        return

    all_seeds: List[int] = []
    for fp in unc_files:
        rows = read_jsonl_maybe_gz(fp)
        for r in rows:
            all_seeds.append(int(r["seed"]))

    all_seeds = sorted(set(all_seeds))
    print(f"Loaded {len(all_seeds)} uncovered seeds across {len(unc_files)} files.")
    print(f"Rechecking with MAX_DEPTH={cfg.MAX_DEPTH}, MOD_BITS={cfg.MOD_BITS}, BASIN_CUTOFF={cfg.BASIN_CUTOFF}")
    print("Mode: NO dominance pruning (direct prune witness only).")
    print()

    monsters = []
    deepest = (0, None)  # (depth, seed)
    witnesses: Dict[int, Dict[str, int]] = {}

    for i, seed in enumerate(all_seeds, start=1):
        is_monster, md, wit = recheck_seed(seed, cfg)
        if md > deepest[0]:
            deepest = (md, seed)

        if is_monster:
            monsters.append(seed)
        else:
            if wit is not None:
                witnesses[seed] = wit

        if i % 1000 == 0:
            print(f"Progress: {i}/{len(all_seeds)}  monsters={len(monsters)}  deepest_seen={deepest[0]} (seed={deepest[1]})")

    print("\n=== RESULT ===")
    print(f"uncovered_seeds_checked: {len(all_seeds)}")
    print(f"monsters_found: {len(monsters)}")
    if monsters:
        print("monster_seeds (first 50):", monsters[:50])
    print(f"deepest_depth_seen: {deepest[0]} (seed={deepest[1]})")
    print(f"direct_prune_witnesses_found: {len(witnesses)}")

    # Write a report you can commit alongside run artifacts
    out = {
        "run_dir": run_dir,
        "MAX_DEPTH": cfg.MAX_DEPTH,
        "MOD_BITS": cfg.MOD_BITS,
        "BASIN_CUTOFF": cfg.BASIN_CUTOFF,
        "uncovered_seeds_checked": len(all_seeds),
        "monsters_found": len(monsters),
        "monster_seeds": monsters[:5000],  # cap to avoid huge json
        "deepest_depth_seen": deepest[0],
        "deepest_seed": deepest[1],
        "direct_prune_witnesses_found": len(witnesses),
    }
    with open(os.path.join(run_dir, "recheck_uncovered_report.json"), "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)

    # Optional: dump witnesses for those uncovered seeds that do prune directly
    with open(os.path.join(run_dir, "recheck_uncovered_witnesses.jsonl"), "w", encoding="utf-8") as f:
        for seed in sorted(witnesses.keys()):
            f.write(json.dumps({"seed": seed, "witness": witnesses[seed]}) + "\n")

    print("\nWrote:")
    print(" - recheck_uncovered_report.json")
    print(" - recheck_uncovered_witnesses.jsonl")

if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--run-dir", required=True)
    args = ap.parse_args()
    main(args.run_dir)
