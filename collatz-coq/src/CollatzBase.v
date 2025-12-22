(* CollatzBase.v *)
From Coq Require Import ZArith Lia.
Open Scope Z_scope.

Set Default Proof Mode "Classic".

(***********************************************************)
(** Standard Collatz step on positive integers (Z)         **)
(***********************************************************)

Definition collatz_step (x : Z) : Z :=
  if Z.even x then x / 2 else 3 * x + 1.

Lemma collatz_step_pos :
  forall x : Z, 0 < x -> 0 < collatz_step x.
Proof.
  intros x Hx.
  unfold collatz_step.
  destruct (Z.even x) eqn:Hev.
  - (* even: x/2 > 0 *)
    assert (Hx2 : 0 < x / 2).
    {
      (* For x>0, x/2 >= 1 when x>=2; handle x=1 separately but 1 is odd anyway. *)
      destruct (Z_lt_ge_dec x 2) as [Hxlt2 | Hxge2].
      + (* x = 1 since x>0 and x<2 *)
        assert (x = 1) by lia.
        subst x.
        (* contradiction: 1 is not even *)
        rewrite Z.even_1 in Hev. discriminate.
      + (* x >= 2 *)
        (* Use Z.div_str_pos: 0 < x and 1 < 2? easier: x/2 >= 1 *)
        assert (1 <= x / 2) by (apply Z.div_le_lower_bound; lia).
        lia.
    }
    exact Hx2.
  - (* odd: 3x+1 > 0 *)
    nia.
Qed.
