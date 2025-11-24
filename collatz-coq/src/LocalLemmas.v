From Coq Require Import ZArith.
Open Scope Z_scope.

(***********************************************************)
(** 2-adic valuation as a relation (simple version)        *)
(***********************************************************)

(* ν₂(x) = v  iff  v >= 0, 2^v | x, and 2^(v+1) ∤ x.
   This is only used to *state* Lemma 1; we don't prove anything
   about it in Coq right now. *)
Definition v2_rel (x v : Z) : Prop :=
  0 <= v /\
  (2 ^ v | x) /\
  ~ (2 ^ (v + 1) | x).

(***********************************************************)
(** Lemma 1: Finite Dependence (statement only)            *)
(***********************************************************)

(* Direct translation of your Lemma 1 into a Prop. *)
Definition Lemma1_statement : Prop :=
  forall (r m n v : Z),
    0 <= r ->
    v2_rel (3 * n + 1) v ->
    v <= r ->
    (m - n) mod (2 ^ (r + 1)) = 0 ->
    v2_rel (3 * m + 1) v.

(***********************************************************)
(** Lemma 2: Dominance (statement only)                    *)
(***********************************************************)

(* Direct translation of your Lemma 2 into a Prop. *)
Definition Lemma2_statement : Prop :=
  forall (A1 A2 t1 t2 b1 b2 : Z),
    A1 >= A2 ->
    t1 <= t2 ->
    b1 >= b2 ->
    (A1 > A2 \/ t1 < t2 \/ b1 > b2) ->
    exists N : Z,
      forall n0 : Z,
        n0 >= N ->
        (A1 * n0 + b1) * 2 ^ (t2 - t1) > (A2 * n0 + b2).
