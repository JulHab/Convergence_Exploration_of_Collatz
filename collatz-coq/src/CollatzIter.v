(* CollatzIter.v *)
From Coq Require Import ZArith Lia.
From Collatz Require Import CollatzBase.
Open Scope Z_scope.

Set Default Proof Mode "Classic".

Fixpoint iter (k : nat) (x : Z) : Z :=
  match k with
  | O => x
  | S k' => iter k' (collatz_step x)
  end.

Lemma iter_add : forall a b x,
  iter (a + b)%nat x = iter b (iter a x).
Proof.
  induction a; intros b x; simpl.
  - reflexivity.
  - rewrite IHa. reflexivity.
Qed.

Definition reaches_1 (x : Z) : Prop :=
  exists k : nat, iter k x = 1.

Lemma iter_pos :
  forall k x, 0 < x -> 0 < iter k x.
Proof.
  induction k; intros x Hx; simpl.
  - exact Hx.
  - apply IHk. apply collatz_step_pos. exact Hx.
Qed.
