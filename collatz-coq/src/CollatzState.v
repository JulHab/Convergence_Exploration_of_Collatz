From Coq Require Import ZArith Lia Bool.
From Collatz Require Import CollatzBase.

Open Scope Z_scope.

Record State := {
  a : Z;
  t : Z;
  A : Z;     (* = 3^a *)
  b : Z;
  n_mod : Z;
  depth : Z;
  v2_last : option Z
}.

Parameter MOD_BITS : Z.
Definition MOD_MASK : Z := 2 ^ MOD_BITS - 1.

(* Universal contraction as in prune_check *)
Parameter BASIN_CUTOFF : Z.

Definition universally_contractive_state (S : State) : bool :=
  let two_t := 2 ^ S.(t) in
  if two_t <=? S.(A) then false else
  let delta := two_t - S.(A) in
  S.(b) <? (BASIN_CUTOFF * delta).

(* Dominance *)
Definition dominates (hard soft : State) : bool :=
  (hard.(A) >=? soft.(A)) &&
  (hard.(t) <=? soft.(t)) &&
  (hard.(b) >=? soft.(b)) &&
  (
    (hard.(A) >? soft.(A)) ||
    (hard.(t) <? soft.(t)) ||
    (hard.(b) >? soft.(b))
  ).
