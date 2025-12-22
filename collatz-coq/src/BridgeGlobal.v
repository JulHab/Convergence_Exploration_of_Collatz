(* BridgeGlobal.v *)
From Coq Require Import ZArith Lia Wellfounded Arith.
From Collatz Require Import CollatzBase CollatzIter.
Open Scope Z_scope.

Set Default Proof Mode "Classic".

(***********************************************************)
(** Bounded descent interface                               **)
(***********************************************************)

(* “Above N, within K steps we strictly decrease.” *)
Definition bounded_descent (N K : Z) : Prop :=
  forall x : Z,
    0 < x ->
    N <= x ->
    exists j : nat,
      (Z.of_nat j <= K)%Z /\
      0 < iter j x < x.

(* Base-range assumption: all positives below N reach 1. *)
Definition base_range_ok (N : Z) : Prop :=
  forall x : Z,
    0 < x < N ->
    reaches_1 x.

(***********************************************************)
(** Descent + base-range ⇒ global convergence               **)
(***********************************************************)

Theorem global_convergence_from_bounded_descent :
  forall (N K : Z),
    1 <= N ->
    bounded_descent N K ->
    base_range_ok N ->
    forall x : Z, 0 < x -> reaches_1 x.
Proof.
  intros N K HN1 HBD Hbase x Hxpos.

  (* Well-founded induction on the natural measure m(x)=to_nat x. *)
  set (m := fun z : Z => Z.to_nat z).
  assert (Hwf : well_founded (fun a b : Z => (m a < m b)%nat)).
  { unfold m. apply (wf_inverse_image Z nat lt Z.to_nat lt_wf). }

  refine (well_founded_induction Hwf (fun y => 0 < y -> reaches_1 y) _ x Hxpos).
  intros y IH Hypos.

  destruct (Z_lt_ge_dec y N) as [Hy_ltN | Hy_geN].
  - (* y < N: base-range *)
    apply Hbase; lia.
  - (* y >= N: apply bounded descent, then recurse on smaller iter j y *)
    assert (HNy : N <= y) by lia.
    destruct (HBD y Hypos HNy) as [j [HjK [Hyj_pos Hyj_lt]]].
    set (y' := iter j y).
    assert (Hy'_pos : 0 < y') by (subst y'; exact Hyj_pos).
    assert (Hy'_lt  : y' < y) by (subst y'; exact Hyj_lt).
    
    (* show measure decreases *)
    assert (Hm : (m y' < m y)%nat).
    {
      unfold m, y'.
      apply Z2Nat.inj_lt; try lia.
    }

    specialize (IH y' Hm Hy'_pos).
    destruct IH as [k Hk].

    (* Compose iterations: iter (j+k) y = iter k (iter j y) *)
    exists (j + k)%nat.
    rewrite iter_add.
    (* iter k y' = 1 *)
    subst y'. exact Hk.
Qed.
