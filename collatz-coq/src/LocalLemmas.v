From Coq Require Import ZArith Znumtheory Lia Psatz.
From Coq Require Import Ring.
From Ltac2 Require Import Ltac2.
Open Scope Z_scope.

Set Default Proof Mode "Classic".

(***********************************************************)
(** 2-adic valuation as a relation (simple version)        *)
(***********************************************************)

Definition v2_rel (x v : Z) : Prop :=
  0 <= v /\
  Z.divide (2 ^ v) x /\
  ~ Z.divide (2 ^ (v + 1)) x.

Lemma pow_divide_prefix :
  forall r t : Z,
    0 <= t <= r + 1 ->
    Z.divide (2 ^ t) (2 ^ (r + 1)).
Proof.
  intros r t [Ht_nonneg Ht_le].
  set (d := r + 1 - t).
  assert (Hd_nonneg : 0 <= d) by (unfold d in *; lia).
  unfold Z.divide.
  exists (2 ^ d).
  replace (r + 1) with (t + d) by (unfold d in *; lia).
  rewrite Z.mul_comm.
  apply Z.pow_add_r; lia.
Qed.

Lemma pow_ge_one :
  forall k : Z,
    0 <= k ->
    1 <= 2 ^ k.
Proof.
  intros k Hk.
  replace 1 with (2 ^ 0) by reflexivity.
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma pow_ge_two :
  forall k : Z,
    1 <= k ->
    2 <= 2 ^ k.
Proof.
  intros k Hk.
  replace 2 with (2 ^ 1) by reflexivity.
  apply Z.pow_le_mono_r; lia.
Qed.

(***********************************************************)
(** Lemma 1: Finite Dependence (statement)                 *)
(***********************************************************)

Definition Lemma1_statement : Prop :=
  forall (r m n v : Z),
    0 <= r ->
    v2_rel (3 * n + 1) v ->
    v <= r ->
    (m - n) mod (2 ^ (r + 1)) = 0 ->
    v2_rel (3 * m + 1) v.

(***********************************************************)
(** Lemma 1 (proved)                                       *)
(***********************************************************)

Lemma Lemma1 : Lemma1_statement.
Proof.
  unfold Lemma1_statement.
  intros r m n v Hr Hv2 Hvr Hmn_mod0.
  unfold v2_rel in *.
  destruct Hv2 as (Hv_nonneg & Hdiv & Hnotdiv).
  split; [exact Hv_nonneg|].
  assert (Hmn_div : Z.divide (2 ^ (r + 1)) (m - n)).
  {
    apply Zmod_divide; try (apply Z.pow_nonzero; lia).
    exact Hmn_mod0.
  }
  assert (Hpow_div :
            forall t : Z,
              0 <= t <= r + 1 ->
              Z.divide (2 ^ t) (m - n)).
  {
    intros t Ht.
    eapply Z.divide_trans.
    - apply pow_divide_prefix; exact Ht.
    - exact Hmn_div.
  }
  assert (Hmul_div :
            forall t : Z,
              Z.divide (2 ^ t) (m - n) ->
              Z.divide (2 ^ t) (3 * (m - n))).
  {
    intros t Ht.
    apply Z.divide_mul_r with (m := 3).
    exact Ht.
  }

  split.
  - assert (Hdiv_3mn_v : Z.divide (2 ^ v) (3 * (m - n))).
    {
      apply Hmul_div.
      apply Hpow_div; lia.
    }
    assert (Hdecomp : 3 * m + 1 = (3 * n + 1) + 3 * (m - n)) by ring.
    rewrite Hdecomp.
    eapply Z.divide_add_r; eauto.

  - intro Hcontra.
    assert (Hdiv_3mn_v1 : Z.divide (2 ^ (v + 1)) (3 * (m - n))).
    {
      apply Hmul_div.
      apply Hpow_div; lia.
    }
    assert (Hdiv_3n1_v1 : Z.divide (2 ^ (v + 1)) (3 * n + 1)).
    {
      replace (3 * n + 1) with ((3 * m + 1) - 3 * (m - n)) by ring.
      eapply Z.divide_sub_r; eauto.
    }
    apply Hnotdiv; exact Hdiv_3n1_v1.
Qed.

(***********************************************************)
(** Lemma 2: Dominance (statement)                         *)
(***********************************************************)

Definition Lemma2_statement : Prop :=
  forall (A1 A2 t1 t2 b1 b2 : Z),
    0 < A1 ->
    A1 >= A2 ->
    t1 <= t2 ->
    b1 >= b2 ->
    (A1 > A2 \/ t1 < t2 \/ b1 > b2) ->
    exists N : Z,
      forall n0 : Z,
        n0 >= N ->
        (A1 * n0 + b1) * 2 ^ (t2 - t1) > (A2 * n0 + b2).

(***********************************************************)
(** Lemma 2 (proved)                                       *)
(***********************************************************)

Lemma Lemma2 : Lemma2_statement.
Proof.
  unfold Lemma2_statement.
  intros A1 A2 t1 t2 b1 b2 HA1pos HA Ht Hb Hstrict.

  set (d := t2 - t1).
  assert (Hd_nonneg : 0 <= d) by (unfold d; lia).

  set (c1 := A1 * 2 ^ d - A2).
  set (c0 := b1 * 2 ^ d - b2).

  assert (Hlin :
            forall n0,
              (A1 * n0 + b1) * 2 ^ d - (A2 * n0 + b2) = c1 * n0 + c0).
  { intro n0; unfold c1, c0, d; ring. }

  assert (Hcoef : c1 > 0 \/ (c1 = 0 /\ c0 > 0)).
  {
    unfold c1, c0, d.
    destruct Hstrict as [HA_strict | [Ht_strict | Hb_strict]].
    - left.
      assert (1 <= 2 ^ (t2 - t1)) by (apply pow_ge_one; lia).
      nia.
    - left.
      assert (t2 - t1 >= 1) by lia.
      assert (2 <= 2 ^ (t2 - t1)) by (apply pow_ge_two; lia).
      nia.
    - destruct (Z_lt_ge_dec t1 t2) as [Htlt | Htge].
      + left.
        assert (t2 - t1 >= 1) by lia.
        assert (2 <= 2 ^ (t2 - t1)) by (apply pow_ge_two; lia).
        nia.
      + assert (t1 = t2) by lia.
        subst t2.
        replace (t1 - t1) with 0 by lia.
        destruct (Z.eq_dec A1 A2) as [Heq | Hneq].
        * right. subst A2. split; nia.
        * left. assert (A1 > A2) by lia. nia.
  }

  destruct Hcoef as [Hc1_pos | [Hc1_zero Hc0_pos]].
  - exists (Z.max 0 (-c0 + 1)).
    intros n0 Hn0.
    assert (Hn0_le : Z.max 0 (-c0 + 1) <= n0) by (apply Z.ge_le; exact Hn0).
    assert (Hn0_nonneg : 0 <= n0).
    { eapply Z.le_trans; [apply Z.le_max_l|exact Hn0_le]. }
    assert (Hn0_ge : -c0 + 1 <= n0).
    { eapply Z.le_trans; [apply Z.le_max_r|exact Hn0_le]. }
    assert (Hn0_bound : 1 <= n0 + c0).
    {
      apply Z.add_le_mono_r with (p := c0) in Hn0_ge.
      replace ((-c0 + 1) + c0) with 1 in Hn0_ge by ring.
      exact Hn0_ge.
    }
    assert (Hterm_nonneg : 0 <= (c1 - 1) * n0).
    { apply Z.mul_nonneg_nonneg; lia. }
    assert (Hsum_pos :
              1 <= (c1 - 1) * n0 + (n0 + c0)).
    {
      replace 1 with (0 + 1) by lia.
      apply Z.add_le_mono; [exact Hterm_nonneg|exact Hn0_bound].
    }
    replace ((c1 - 1) * n0 + (n0 + c0)) with (c1 * n0 + c0) in Hsum_pos by ring.
    assert (Hpos : 0 < c1 * n0 + c0) by lia.
    specialize (Hlin n0).
    assert (Hpos' :
              0 < (A1 * n0 + b1) * 2 ^ d - (A2 * n0 + b2)).
    { rewrite Hlin; exact Hpos. }
    lia.
  - exists 0.
    intros n0 Hn0.
    specialize (Hlin n0).
    assert (Hpos' :
              0 < (A1 * n0 + b1) * 2 ^ d - (A2 * n0 + b2)).
    {
      rewrite Hlin.
      rewrite Hc1_zero.
      lia.
    }
    lia.
Qed.
