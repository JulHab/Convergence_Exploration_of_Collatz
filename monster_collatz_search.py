import math
import json
import os
from collections import deque, defaultdict
from dataclasses import dataclass, asdict
from typing import Optional, List, Dict, Tuple

# ============================================================
# 1. CONFIG
# ============================================================

@dataclass
class RunConfig:
    BASIN_CUTOFF: int      # n0 must be >= this for "universal contraction"
    MAX_DEPTH: int         # if a branch survives this many macro-steps unpruned => monster
    MOD_BITS: int          # how many low bits of n we track at each step
    INIT_BITS: int         # how many low bits of the initial n0 we seed
    BATCH_SIZE: int        # how many residues per batch
    DEPTH_LOG_THRESHOLD: int  # print progress only after this depth
    OUTPUT_DIR: str        # where to dump all artifacts

def make_default_config() -> RunConfig:
    return RunConfig(
        BASIN_CUTOFF = 1_000_000,
        MAX_DEPTH = 300,
        MOD_BITS = 40,
        INIT_BITS = 30,
        BATCH_SIZE = 1_000_000,
        DEPTH_LOG_THRESHOLD = 120,
        OUTPUT_DIR = "run_INIT30_MOD40"
    )

# ============================================================
# 2. CORE MATH MODEL
# ============================================================

def trailing_zeros_2(x: int) -> int:
    """Return ν₂(x): the exponent of 2 in x (number of trailing zero bits)."""
    c = 0
    while (x & 1) == 0:
        x >>= 1
        c += 1
    return c

@dataclass
class State:
    """
    Symbolic Collatz prefix state.

    We encode the value after `depth` macro-steps as:

        n(depth) = (A * n0 + b) / 2^t

    where:
        - a  = number of odd (3n+1) steps so far
        - t  = total number of factor-2 divisions so far
        - A  = 3^a  (this is enforced algebraically)
        - b  = accumulated affine offset
        - n_mod = current n(depth) modulo 2^MOD_BITS
        - v2_last = ν₂(3n+1) used at the most recent odd step
                    (None if the last step was even)

    This representation lets us talk about *all* starting n0 at once.
    """
    a: int
    t: int
    A: int         # should always equal 3**a
    b: int
    n_mod: int
    depth: int
    parent: Optional["State"]
    v2_last: Optional[int]

    def key_for_registry(self) -> Tuple[int, int]:
        return (self.n_mod, self.depth)

def assert_state_invariants(st: State):
    # Debug-facing invariant check. This can be turned off in production.
    # Ensures internal algebra hasn't drifted.
    if pow(3, st.a) != st.A:
        raise RuntimeError(f"Invariant A=3^a violated at depth {st.depth}")

def prune_check(st: State, cfg: RunConfig) -> bool:
    """
    Universal contraction test.

    After this prefix we have:
        n = (3^a * n0 + b) / 2^t.

    If 2^t > 3^a and b / (2^t - 3^a) < BASIN_CUTOFF,
    then for *every* n0 >= BASIN_CUTOFF we get n < n0.

    In that case, THIS PREFIX ALONE proves 'you are coming down',
    so we do not need to extend this branch further.
    """
    A = st.A
    two_t = 1 << st.t
    if two_t <= A:
        return False

    delta = two_t - A  # strictly >0 now
    # we want b / delta < BASIN_CUTOFF  <=>  b < BASIN_CUTOFF * delta
    if st.b < cfg.BASIN_CUTOFF * delta:
        return True
    return False

def step_once(st: State, cfg: RunConfig, mod_mask: int) -> State:
    """
    Advance one macro-step of the Collatz map, but symbolically.

    Rule per macro-step:
      - If n is even:    n -> n/2 (exactly one halving)
      - If n is odd:     n -> (3n+1)/2^v, where v = ν₂(3n+1)

    We update:
      a, t, A=3^a, b, n_mod, depth, v2_last
    """
    a = st.a
    t = st.t
    A = st.A
    b = st.b
    n_mod = st.n_mod
    depth = st.depth

    if (n_mod & 1) == 0:
        # even step: divide by 2 exactly once
        new_a = a
        new_t = t + 1
        new_A = A
        new_b = b
        new_n_mod = (n_mod >> 1) & mod_mask
        v2_used = None
    else:
        # odd step: n -> (3n+1)/2^v, v = ν₂(3n+1)
        tmp = 3 * n_mod + 1
        tmp_masked = tmp & mod_mask

        if tmp_masked == 0:
            # Means (3*n_mod+1) is 0 mod 2^MOD_BITS.
            # Actual ν₂(tmp) >= MOD_BITS. We conservatively
            # take v_local = MOD_BITS. This is allowed because
            # *larger* v only makes the branch 'easier to kill'.
            v_local = cfg.MOD_BITS
        else:
            v_local = trailing_zeros_2(tmp_masked)

        new_a = a + 1
        new_t = t + v_local
        new_A = A * 3
        # Derivation:
        # n_old = (A n0 + b)/2^t
        # 3 n_old + 1 = (3A n0 + 3b + 2^t)/2^t
        # divide by 2^v_local:
        # => n_new = (3A n0 + 3b + 2^t)/2^(t+v_local)
        new_b = 3 * b + (1 << t)

        new_n_mod = (tmp_masked >> v_local) & mod_mask
        v2_used = v_local

    nxt = State(
        a=new_a,
        t=new_t,
        A=new_A,
        b=new_b,
        n_mod=new_n_mod,
        depth=depth + 1,
        parent=st,
        v2_last=v2_used
    )

    # Optional safety check
    # assert_state_invariants(nxt)

    return nxt

def dominates(hard: State, soft: State) -> bool:
    """
    Dominance partial order.

    We say 'hard' dominates 'soft' if hard is at least as "resistant
    to pruning" in all three of these senses (and strictly better in ≥1):

      - Larger A = 3^a  (more multiplicative growth)
      - Smaller t       (fewer halvings so far)
      - Larger b        (bigger offset, can keep threshold higher)

    Intuition:
      If 'hard' dominates 'soft', then any future extension of 'soft'
      cannot survive pruning longer than some extension of 'hard',
      so 'soft' is redundant and can be discarded.
    """
    cond = (
        (hard.A >= soft.A) and
        (hard.t <= soft.t) and
        (hard.b >= soft.b)
    )
    strict = (
        (hard.A > soft.A) or
        (hard.t < soft.t) or
        (hard.b > soft.b)
    )
    return cond and strict

def summarize_state_math(st: State) -> Dict[str, float]:
    """
    Produce a dictionary of human-readable diagnostics for a state.
    This is what we log in 'deep_snapshots' and final summaries.
    """
    two_t = 1 << st.t
    delta = two_t - st.A
    has_contract = (delta > 0)
    threshold_est = (st.b / delta) if has_contract else None
    tension = (st.t / (st.a * math.log2(3))) if st.a > 0 else None

    return {
        "depth": st.depth,
        "a": st.a,
        "t": st.t,
        "A": st.A,
        "b": st.b,
        "delta": delta,
        "has_contract": has_contract,
        "threshold_est": threshold_est,
        "tension": tension,
        "n_mod": st.n_mod,
        "v2_last": st.v2_last,
    }

def reconstruct_path(leaf: Optional[State]) -> List[State]:
    """
    Follow parent pointers back to the root and reverse.
    """
    out = []
    cur = leaf
    while cur is not None:
        out.append(cur)
        cur = cur.parent
    out.reverse()
    return out

# ============================================================
# 3. BATCH SEARCH
# ============================================================

@dataclass
class BatchResult:
    monster_found: bool
    batch_max_depth: int
    deepest_path: List[State]
    deep_snapshots: List[Dict[str, float]]
    survivors_at_depth: Dict[int, int]
    monster_path: Optional[List[State]]
    max_v2_seen: int

def run_batch(cfg: RunConfig,
              seed_start: int,
              seed_end: int) -> BatchResult:
    """
    Explore all starting residues n0 in [seed_start, seed_end),
    each interpreted as "n0 mod 2^INIT_BITS = residue", lifted into
    our symbolic form.

    We BFS/DFS-like through the symbolic Collatz graph, pruning:
      - states that already enforce universal contraction,
      - states dominated by a nastier state at same (n_mod, depth).

    We track:
      - whether anything survives past cfg.MAX_DEPTH (monster)
      - the deepest state reached
      - ν₂ bursts along that deepest path
    """

    MOD_MASK = (1 << cfg.MOD_BITS) - 1

    q = deque()
    frontier_registry = defaultdict(list)

    batch_max_depth = 0
    survivors_at_depth: Dict[int, int] = {}
    monster_found = False
    monster_path = None

    best_depth_this_batch = -1
    deepest_state_this_batch = None
    deep_snapshots: List[Dict[str, float]] = []
    max_v2_seen = 0

    # Initialize seeds for this batch
    for residue in range(seed_start, seed_end):
        st0 = State(
            a=0,
            t=0,
            A=1,
            b=0,
            n_mod=(residue & MOD_MASK),
            depth=0,
            parent=None,
            v2_last=None
        )
        q.append(st0)
        frontier_registry[(st0.n_mod, 0)].append(st0)
        survivors_at_depth[0] = survivors_at_depth.get(0, 0) + 1

    while q:
        st = q.popleft()
        d = st.depth
        if d > batch_max_depth:
            batch_max_depth = d

        # Monster detection: survived "too long" without pruning
        if d >= cfg.MAX_DEPTH:
            monster_found = True
            monster_path = reconstruct_path(st)
            break

        # Universal contraction => prune branch
        if prune_check(st, cfg):
            continue

        # Advance one macro-step
        nxt = step_once(st, cfg, MOD_MASK)
        nd = nxt.depth

        # Update best depth / snapshots
        if nd > best_depth_this_batch:
            best_depth_this_batch = nd
            deepest_state_this_batch = nxt

            snap = summarize_state_math(nxt)
            deep_snapshots.append(snap)

            if nxt.v2_last is not None and nxt.v2_last > max_v2_seen:
                max_v2_seen = nxt.v2_last

            if nd >= cfg.DEPTH_LOG_THRESHOLD:
                print(f"[{seed_start}:{seed_end}) NEW BEST DEPTH {nd}")
                print("   a =", snap["a"], "t =", snap["t"])
                print("   delta =", snap["delta"])
                print("   has_contract =", snap["has_contract"],
                      "threshold_est ~", snap["threshold_est"])
                print("   tension ~", snap["tension"])
                print("   last v2 burst =", snap["v2_last"])
                print("   n_mod =", snap["n_mod"])
                print()

        # Dominance filtering at key (n_mod, depth)
        key = (nxt.n_mod, nd)

        keep = True
        new_bucket = []
        for old in frontier_registry[key]:
            if dominates(old, nxt):
                # an existing state is strictly nastier => drop nxt
                keep = False
                break

        if keep:
            # remove states that nxt dominates
            for old in frontier_registry[key]:
                if not dominates(nxt, old):
                    new_bucket.append(old)

            new_bucket.append(nxt)
            frontier_registry[key] = new_bucket

            q.append(nxt)
            survivors_at_depth[nd] = survivors_at_depth.get(nd, 0) + 1

    deepest_path = reconstruct_path(deepest_state_this_batch) if deepest_state_this_batch else []

    # safety: recompute max_v2 on that deepest_path
    for node in deepest_path:
        if node.v2_last is not None and node.v2_last > max_v2_seen:
            max_v2_seen = node.v2_last

    return BatchResult(
        monster_found=monster_found,
        batch_max_depth=batch_max_depth,
        deepest_path=deepest_path,
        deep_snapshots=deep_snapshots,
        survivors_at_depth=survivors_at_depth,
        monster_path=monster_path,
        max_v2_seen=max_v2_seen
    )

# ============================================================
# 4. DRIVER
# ============================================================

def ensure_output_dir(cfg: RunConfig):
    os.makedirs(cfg.OUTPUT_DIR, exist_ok=True)

def write_path_summary(path: List[State], filename: str):
    with open(filename, "w") as f:
        f.write("depth,a,t,v2_last,n_mod,delta,threshold\n")
        for node in path:
            two_t = (1 << node.t)
            delta = two_t - node.A
            has_contract = (two_t > node.A)
            thresh = (node.b / delta) if has_contract else None
            f.write(f"{node.depth},{node.a},{node.t},"
                    f"{node.v2_last},{node.n_mod},"
                    f"{delta},{thresh}\n")

def write_v2_profile(path: List[State], max_v2: int, filename: str):
    with open(filename, "w") as f:
        f.write("depth,v2_last\n")
        for node in path:
            f.write(f"{node.depth},{node.v2_last}\n")
        f.write(f"\n# max_v2_on_path = {max_v2}\n")

def write_snapshots(snaps: List[Dict[str, float]], filename: str):
    with open(filename, "w") as f:
        f.write("depth,a,t,delta,has_contract,threshold_est,tension,v2_last,n_mod\n")
        for s in snaps:
            f.write(
                f"{s['depth']},{s['a']},{s['t']},"
                f"{s['delta']},{s['has_contract']},"
                f"{s['threshold_est']},{s['tension']},"
                f"{s['v2_last']},{s['n_mod']}\n"
            )

def write_config(cfg: RunConfig):
    with open(os.path.join(cfg.OUTPUT_DIR, "config.json"), "w") as f:
        json.dump(asdict(cfg), f, indent=2)

def driver():
    cfg = make_default_config()
    ensure_output_dir(cfg)
    write_config(cfg)

    INIT_MOD = 1 << cfg.INIT_BITS
    total_batches = (INIT_MOD + cfg.BATCH_SIZE - 1) // cfg.BATCH_SIZE

    print(f"INIT_BITS={cfg.INIT_BITS} => {INIT_MOD} residues total.")
    print(f"Processing in {total_batches} batches of size {cfg.BATCH_SIZE}.\n")

    global_best_depth = -1
    global_best_path: List[State] = []
    global_best_batch_range = None
    global_best_snaps: List[Dict[str, float]] = []
    global_max_v2 = 0

    any_monster = False
    first_monster_info = None  # (batch_range, depth, max_v2, path)

    for batch_i, start in enumerate(range(0, INIT_MOD, cfg.BATCH_SIZE)):
        end = min(start + cfg.BATCH_SIZE, INIT_MOD)
        print(f"=== BATCH {batch_i+1}/{total_batches} [{start}:{end}) ===")

        res = run_batch(cfg, start, end)

        print(f"Batch [{start}:{end}) done.")
        print("  batch_max_depth:", res.batch_max_depth)
        print("  monster_found:", res.monster_found)
        print("  max_v2_seen:", res.max_v2_seen)
        print()

        if res.monster_found and not any_monster:
            any_monster = True
            depth_monster = res.monster_path[-1].depth if res.monster_path else None
            first_monster_info = ((start, end), depth_monster, res.max_v2_seen, res.monster_path)

        if res.batch_max_depth > global_best_depth:
            global_best_depth = res.batch_max_depth
            global_best_path = res.deepest_path
            global_best_batch_range = (start, end)
            global_best_snaps = res.deep_snapshots
            global_max_v2 = res.max_v2_seen

    # Final reporting
    print("\n=== GLOBAL SUMMARY ===")
    print("Any monster?:", any_monster)
    print("Deepest depth overall:", global_best_depth)
    print("That depth came from batch range:", global_best_batch_range)
    print("Global max ν2 burst on that path:", global_max_v2)

    # Write global report
    with open(os.path.join(cfg.OUTPUT_DIR, "global_report.txt"), "w") as f:
        f.write(f"any_monster={any_monster}\n")
        f.write(f"deepest_depth_overall={global_best_depth}\n")
        f.write(f"best_batch_range={global_best_batch_range}\n")
        f.write(f"global_max_v2={global_max_v2}\n")

        if any_monster and first_monster_info:
            (rng, dmonster, v2m, mpath) = first_monster_info
            f.write("\nmonster_batch_range=" + str(rng) + "\n")
            f.write("monster_depth=" + str(dmonster) + "\n")
            f.write("monster_max_v2=" + str(v2m) + "\n")

    # Write deepest path data
    write_path_summary(
        global_best_path,
        os.path.join(cfg.OUTPUT_DIR, "deepest_path_summary.txt")
    )

    write_v2_profile(
        global_best_path,
        global_max_v2,
        os.path.join(cfg.OUTPUT_DIR, "deepest_path_v2.txt")
    )

    write_snapshots(
        global_best_snaps,
        os.path.join(cfg.OUTPUT_DIR, "deep_snapshots.txt")
    )

    # Also, if we *did* see any monster (depth >= MAX_DEPTH), dump that path
    if any_monster and first_monster_info:
        (_, _, _, mpath) = first_monster_info
        if mpath:
            write_path_summary(
                mpath,
                os.path.join(cfg.OUTPUT_DIR, "monster_path.txt")
            )

if __name__ == "__main__":
    driver()
