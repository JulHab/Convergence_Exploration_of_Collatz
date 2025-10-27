# Bounded Descent and Symbolic 2-Adic Dynamics in the Collatz Map

**Author:** Julian Haberkorn  
**Institution:** Independent Researcher, Berlin, Germany  
**Paper:** [Bounded Descent and Symbolic 2–Adic Dynamics in the Collatz Map (PDF)](./Symbolic_and_Computational_Exploration_of_the_Collatz_Map.pdf)  
**Date:** October 2025  

---

## 🧩 Overview

This repository contains the implementation, configuration, and computational certificates associated with the paper  
**“Bounded Descent and Symbolic 2-Adic Dynamics in the Collatz Map.”**

The project introduces a **finite symbolic model** of the Collatz iteration expressed in 2-adic form.  
By combining three provable lemmas —

1. **Finite Dependence** — local behaviour depends only on finitely many low bits;  
2. **Dominance** — dominated symbolic states can be safely pruned;  
3. **Bounded Descent** — every undominated branch contracts within a finite bound K;

— the infinite Collatz process is reduced to a finite enumeration of symbolic prefixes.

A deterministic breadth-first search explores all residue classes up to a chosen bit-depth, applies dominance and contraction tests, and produces a **finite certificate** of convergence.

---

## 📈 Key Results

| Parameter | Symbol | Value |
|------------|---------|-------|
| Initial residue bits | `INIT_BITS` | 28, 30 |
| Modulus precision | `MOD_BITS` | 40 |
| Maximum search depth | `MAX_DEPTH` | 300 |
| Observed maximal depth | `K*` | **237** |
| Max 2-adic burst `ν₂(3n+1)` | ≤ 10 (global), 6 (on deepest branch) |
| Undominated survivors | 0 |
| Verified base range | N = 10⁶  (inside verified range up to 2⁶⁸ ≈ 3×10²⁰ \[[Oliveira e Silva et al., 2011](https://doi.org/10.1090/S0025-5718-2010-02413-X)\]) |

The search shows that **no non-contractive branch** survives beyond depth 237 even when seeding all 2³⁰ residue classes.  
This provides a reproducible **bounded-descent certificate** consistent with universal Collatz convergence.

---

## 🧠 Repository Structure
│ ├── run_INIT28_MOD40/
│ │ ├── config.json
│ │ ├── deep_snapshots.txt
│ │ ├── deepest_path_summary.txt
│ │ ├── deepest_path_v2.txt
│ │ └── global_report.txt
│ ├── run_INIT30_MOD40/
│ │ ├── config.json
│ │ ├── deep_snapshots.txt
│ │ ├── deepest_path_summary.txt
│ │ ├── deepest_path_v2.txt
│ │ └── global_report.txt
├── Symbolic_and_Computational_Exploration_of_the_Collatz_Map.pdf
├── src/
│ ├── collatz_monster_search.py # Main BFS implementation
└── README.md

---

## ⚙️ Reproducing the Search

### 1. Requirements
- Python ≥ 3.10  
- `mpmath`, `numpy`, `pandas`, `argparse`  
- (optional) multicore support via `multiprocessing`

### 2. Run
```bash
python3 src/collatz_monster_search.py --config config.json
