(* CollatzCore.v *)
From Coq Require Import ZArith Lia Psatz Ring.
Open Scope Z_scope.

(*
  CollatzCore: symbolic mechanics + dominance monotonicity + contraction ⇒ descent.

  Symbolic state represents an affine prefix:
    x ↦ (A*x + b) / 2^t

  The key contraction predicate is:
    delta := 2^t - A  is positive
    b < N * delta

  Then for all x >= N, we get strict descent:
    (A*x + b)/2^t < x
*)

(***********************************************************)
(** Symbolic state                                          **)
(***********************************************************)

Record SymState := {
  A_s : Z;
  t_s : Z;
  b_s : Z
}.

Definition pow2 (t : Z) : Z := 2 ^ t.

Definition delta (st : SymState) : Z :=
  pow2 (t_s st) - A_s st.

Definition sym_eval (st : SymState) (x : Z) : Z :=
  (A_s st * x + b_s st) / pow2 (t_s st).

(***********************************************************)
(** Dominance                                               **)
(***********************************************************)

(* “hard dominates soft” = hard is harder (bigger A, smaller t, bigger b). *)
Definition dominates (hard soft : SymState) : Prop :=
  A_s hard >= A_s soft /\
  t_s hard <= t_s soft /\
  b_s hard >= b_s soft.

(***********************************************************)
(** Contraction predicate                                   **)
(***********************************************************)

Definition contracts (N : Z) (st : SymState) : Prop :=
  0 < N /\
  0 <= t_s st /\
  0 < delta st /\
  b_s st < N * delta st.

(***********************************************************)
(** Basic arithmetic lemmas                                 **)
(***********************************************************)

Lemma pow_pos_2 :
  forall t : Z, 0 <= t -> 0 < 2 ^ t.
Proof.
  intros t Ht.
  apply Z.pow_pos_nonneg; lia.
Qed.

Lemma pow2_mono :
  forall a b : Z,
    0 <= a ->
    a <= b ->
    2 ^ a <= 2 ^ b.
Proof.
  intros a b Ha Hab.
  (* Z.pow_le_mono_r requires base >= 0 and 1 <= base *)
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma delta_monotone :
  forall hard soft,
    dominates hard soft ->
    0 <= t_s hard ->
    0 <= t_s soft ->
    delta soft >= delta hard.
Proof.
  intros hard soft Hdom Hth_nonneg Hts_nonneg.
  unfold dominates in Hdom.
  destruct Hdom as [HA [Ht Hb]].
  unfold delta, pow2.

  (* 2^(t_h) <= 2^(t_s) since t_h <= t_s *)
  assert (Hp : 2 ^ (t_s hard) <= 2 ^ (t_s soft)).
  { apply pow2_mono; lia. }

  (* delta soft - delta hard = (2^t_soft - 2^t_hard) + (A_hard - A_soft) >= 0 *)
  assert (Hdiff_nonneg :
            0 <= (2 ^ (t_s soft) - 2 ^ (t_s hard)) + (A_s hard - A_s soft)).
  {
    apply Z.add_nonneg_nonneg.
    - lia.
    - lia.
  }

  (* Rearrange to target inequality *)
  nia.
Qed.

Lemma contracts_monotone :
  forall N hard soft,
    dominates hard soft ->
    contracts N hard ->
    0 <= t_s soft ->
    contracts N soft.
Proof.
  intros N hard soft Hdom Hc Hts_nonneg.
  pose proof Hdom as Hdom0.
  unfold dominates in Hdom.
  destruct Hdom as [HA [Ht Hb]].
  destruct Hc as [HNpos [Hth_nonneg [Hdh_pos Hbh_lt]]].

  unfold contracts.
  repeat split.
  - exact HNpos.
  - exact Hts_nonneg.
  - (* delta soft > 0 *)
    assert (Hdelta_ge : delta soft >= delta hard).
    { apply delta_monotone; try lia; exact Hdom0. }
    lia.
  - (* b_soft < N * delta_soft *)
    assert (Hdelta_ge : delta soft >= delta hard).
    { apply delta_monotone; try lia; exact Hdom0. }

    assert (Hbs_lt : b_s soft < N * delta soft).
    { nia. }

    exact Hbs_lt.
Qed.

(***********************************************************)
(** Contraction implies descent                             **)
(***********************************************************)

Lemma contracts_implies_descent :
  forall N st x,
    contracts N st ->
    x >= N ->
    sym_eval st x < x.
Proof.
  intros N st x Hc Hx_ge.
  destruct Hc as [HNpos [Ht_nonneg [Hdelta_pos Hb_lt]]].

  set (d := 2 ^ (t_s st)).
  assert (Hd_pos : 0 < d).
  { unfold d. apply pow_pos_2; exact Ht_nonneg. }

  (* delta >= 0 for monotone multiplication *)
  assert (Hdelta_nonneg : 0 <= delta st) by lia.

  (* From x >= N and delta >= 0: N*delta <= x*delta *)
  assert (Hmul_le : N * delta st <= x * delta st).
  { apply Z.mul_le_mono_nonneg_r; lia. }

  (* b < N*delta <= x*delta *)
  assert (Hb_lt_xdelta : b_s st < x * delta st) by lia.

  (* Expand x*delta = x*(d - A) to derive A*x + b < d*x *)
  assert (Hlin_lt_dx : A_s st * x + b_s st < d * x).
  {
    (* rewrite delta *)
    assert (Hb_lt_xdA : b_s st < x * (d - A_s st)).
    {
      unfold delta, pow2 in Hb_lt_xdelta.
      subst d.
      exact Hb_lt_xdelta.
    }

    (* add A*x to both sides *)
    assert (Htmp : A_s st * x + b_s st < A_s st * x + x * (d - A_s st)).
    { apply Z.add_lt_mono_l. exact Hb_lt_xdA. }

    (* simplify RHS to x*d, then commute to d*x *)
    assert (Hrhs : A_s st * x + x * (d - A_s st) = x * d) by ring.
    assert (Htmp2 : A_s st * x + b_s st < x * d).
    { rewrite Hrhs in Htmp. exact Htmp. }

    replace (d * x) with (x * d) by ring.
    exact Htmp2.
  }

  (* Use division upper bound: 0<d and numerator < d*x => numerator/d < x *)
  unfold sym_eval.
  apply (Z.div_lt_upper_bound _ _ _ Hd_pos).
  exact Hlin_lt_dx.
Qed.
