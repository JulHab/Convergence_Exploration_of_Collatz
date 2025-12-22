# Collatz Conjecture — Bounded Descent via Symbolic 2-Adic Dynamics

This repository contains a finite, reproducible bounded-descent certificate for the Collatz map together with a mechanically verified reduction from bounded descent to global convergence.

The project combines:

- a symbolic 2-adic formulation of Collatz trajectories,
- dominance-based pruning of symbolic branches,
- a deterministic external certificate generator and checker,
- and a Coq development that verifies the mathematics and derives global convergence from bounded descent.

The result reduces the Collatz conjecture to the verification of a finite, auditable certificate plus a finite base-range check.

---

## What Is Proven (Precisely)

### Proven inside Coq (kernel-checked)

The following components are fully formalized and checked by the Coq kernel:

1. Symbolic Collatz semantics  
   Exact affine form  
   n_j = (3^a_j * n_0 + b_j) / 2^t_j  

   Including:
   - correct propagation of symbolic states,
   - correct handling of odd/even steps.

2. Dominance pruning  
   If one symbolic state is provably harder than another, the dominated state can be safely discarded.  
   No pruned state can conceal a strictly harder branch.

3. Universal contraction criterion  
   If  
   2^t_j > 3^a_j  
   and  
   b_j < N * (2^t_j − 3^a_j)  

   then all x ≥ N strictly decrease after that prefix.

4. Bounded descent implies global convergence  
   If every x ≥ N decreases within at most K macro-steps, and  
   all 0 < x < N reach 1,  
   then all positive integers reach 1.

   This is formalized as the theorem:
   global_convergence_from_bounded_descent

---

## What Is Verified by Computation

A deterministic external checker validates a finite certificate asserting:

- complete coverage of all residues modulo 2^30,
- existence of a contracting symbolic branch for each residue,
- maximal non-contractive depth K = 237,
- correctness of all dominance and contraction conditions,
- explicit coverage completeness (no residue silently omitted).

The checker produces cryptographically pinned artifacts:

- bucket_acceptance.json
- coverage_report.json
- SHA-256 file hashes
- rolling BLAKE2b commitments (order-sensitive and order-independent)

These outputs are consumed only through a small acceptance interface inside Coq.

---

## Trust Boundary (Explicit)

This project deliberately separates formal logic from external computation.

### Trusted (inside Coq)

- All algebraic lemmas
- Dominance logic
- Bounded descent to convergence theorem
- Consumption of a bounded_descent N K hypothesis

### Assumed / externally checked

- Correctness of the certificate generator
- Correctness of the certificate checker
- Correctness of the coverage check over 2^30 residues
- Correctness of the finite base-range verification below N = 10^6

These assumptions are explicit, isolated, and replaceable.  
No part of the argument depends on hidden computation.

---

## Repository Structure
```
Convergence_Exploration_of_Collatz-1.1.0/
│
├── collatz-coq/ # Coq formalization
│ ├── src/
│ │ ├── BridgeGlobal.v # bounded descent ⇒ global convergence bridge
│ │ ├── CheckerSpec.v # pinned acceptance reports / trust boundary
│ │ ├── CollatzBase.v # core Collatz definitions
│ │ ├── CollatzCore.v # symbolic core / pruning / contraction logic
│ │ ├── CollatzIter.v # iteration semantics
│ │ ├── LocalLemmas.v # local 2-adic / arithmetic lemmas
│ │ └── MainTheorem.v # main theorem packaging
│ ├── _CoqProject
│ └── Makefile
│
├── run_INIT28_MOD40/ # run artifacts (INIT_BITS=28, MOD_BITS=40)
│ └── ... # older certificate style | still inside for completeness
│
├── run_INIT30_MOD40/ # run artifacts (INIT_BITS=30, MOD_BITS=40)
│ ├── batch_summaries.jsonl
│ ├── bucket_acceptance.json
│ ├── bucket_keys_u64.sorted.uniq.bin
│ ├── config.json
│ ├── coverage_report.json
│ ├── min_bucket_witnesses.jsonl.gz
│ ├── minimized.db
│ ├── recheck_uncovered_report.json
│ ├── recheck_uncovered_witnesses.jsonl
│ ├── report.json
│ └── tmp_keys/ # temporary chunk files (optional, can be deleted)
│
│
├── verify_certificate.py # certificate validity + coverage checker (RAM-safe)
├── recheck_uncovered.py # uncovered-seed recheck tooling
├── monster_collatz_search.py # “monster” search / diagnostics
├── minimize_from_v_sqlite.py # minimizer tooling (SQLite-based)
├── hashes.txt # SHA-256 fingerprints of key artifacts
├── README.md # project overview and reproduction steps
└── Symbolic_and_Computational_Exploration_of_the_Collatz_Map.pdf
```
## Reproducibility

### Requirements

- Python ≥ 3.10
- Coq (version recorded in the repository)
- Sufficient disk space (certificate files are large)

### Certificate verification

python verify_certificate.py \
  --dir run_INIT30_MOD40 \
  --build-index \
  --check-coverage

This produces:

- bucket_acceptance.json
- coverage_report.json

Verify SHA-256 hashes against those recorded in the paper.

### Coq verification

make

Successful compilation of MainTheorem.v confirms:

Collatz_converges_from_acceptance

---

## What This Project Is (and Is Not)

### This is

- A finite reduction of Collatz convergence to bounded descent
- A mechanically verified symbolic framework
- A reproducible, auditable computational certificate
- A clean separation between logic and computation

### This is not

- A purely analytic proof
- A proof that avoids all external computation
- A claim that Coq itself enumerates 2^30 residues

Those distinctions are intentional and documented.

---

## Status

- Symbolic bounded descent verified for all residues modulo 2^30
- Maximum non-contractive depth observed: 237
- Universal contraction verified for all x ≥ 10^6
- Global convergence follows from:
  1. the verified bounded-descent certificate, and
  2. a finite base-range check below 10^6

---

## Citation

If you reference this work, please cite the accompanying paper and repository.  
A Zenodo DOI is provided for archival stability.

---

## Notes for Reviewers

- All assumptions are explicit
- All computation is deterministic and replayable
- No heuristic pruning is used
- Any counterexample must manifest as a concrete certificate failure
