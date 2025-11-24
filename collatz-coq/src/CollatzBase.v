From Coq Require Import ZArith Lia.

Open Scope Z_scope.

(* Basic Collatz step on integers *)
Definition collatz_step (n : Z) : Z :=
  if Z.even n then n / 2 else (3 * n + 1) / 2.

(* Abstract 2-adic valuation ν₂: we won't use it concretely yet,
   so we declare it as a parameter with a basic property. *)
Parameter v2 : Z -> Z.

Axiom v2_nonneg : forall x, 0 <= v2 x.
