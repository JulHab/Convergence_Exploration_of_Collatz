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
| Verified base range | N = 10⁶  (inside verified range up to 10^8 \[[Gary T. Leavens, Michael Vermeulen.](https://doi.org/10.1016/0898-1221(92)90034-F6)\]) |

The search shows that **no non-contractive branch** survives beyond depth 237 even when seeding all 2³⁰ residue classes.  
This provides a reproducible **bounded-descent certificate** consistent with universal Collatz convergence.

---

## 🧠 Repository Structure
```bash
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
├── collatz_monster_search.py # Main BFS implementation
└── README.md
```

---

## ⚙️ Reproducing the Search

### 1. Requirements
- Python ≥ 3.10  
- `mpmath`, `numpy`, `pandas`, `argparse`  
- (optional) multicore support via `multiprocessing`

### 2. Run
```bash
python3 src/collatz_monster_search.py --config config.json
```
### 3. Output

A deterministic log and certificate in the same directory.

Identical input produces identical hashes and summaries on all machines.

🔍 Verification

The computational search implements the hypotheses of the formal lemmas:

Finite Dependence: verified empirically with max ν₂ ≤ 10.

Dominance: ensured by lexicographic pruning of symbolic states.

Bounded Descent: confirmed by exhaustion—no undominated branch
remains at depth ≥ 237.

Replication or formalisation in a proof assistant (Lean 4 or Coq)
requires only verifying that the supplied certificate satisfies
these finite conditions.

🧮 Formal Proof Framework

The associated paper proves:

If the above lemmas hold for some finite K and N, and all x < N
are known to reach 1 (verified empirically up to 2⁶⁸ ≈ 3×10²⁰),
then every positive integer eventually reaches 1.

Formal verification would involve:

Encoding the three lemmas in Lean 4 / Coq.

Importing this repository’s certificate data.

Mechanically confirming that no branch violates the inequalities.

📜 Citation

If you use or build upon this work, please cite:

Julian Haberkorn (2025).
Bounded Descent and Symbolic 2-Adic Dynamics in the Collatz Map.
Independent Research Report, Berlin.
[ DOI: 10.5281/zenodo.17463315].

BibTeX:
```bash
@misc{Haberkorn2025Collatz,
  author       = {Julian Haberkorn},
  title        = {Bounded Descent and Symbolic 2--Adic Dynamics in the Collatz Map},
  year         = {2025},
  note         = {Independent Research, Berlin},
  url          = {}
}
```
📬 Contact

For questions or collaboration (e.g., formal verification in Lean/Coq):
Julian Haberkorn — Berlin, Germany
Email: [haberkornj@posteo.de]

🧠 References

Gary T. Leavens, Michael Vermeulen. 3x + 1 Search Programs Computers Mathematics
with Applications 24 (11) (1992): 79–99. https://doi.org/10.1016/
0898-1221(92)90034-F
6

J. C. Lagarias, The 3x+1 problem and its generalizations,
American Mathematical Monthly, 92(1), 3–23 (1985).

R. Terras, A stopping time problem on the positive integers,
Acta Arithmetica, 30(3), 241–252 (1976).

G. J. Wirsching, The dynamical system generated by the 3n+1 function,
Lecture Notes in Mathematics, Vol. 1681, Springer-Verlag, 1998.
