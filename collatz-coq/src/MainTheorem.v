(* MainTheorem.v *)
From Coq Require Import ZArith Lia.
From Collatz Require Import
  CollatzIter
  BridgeGlobal
  CheckerSpec.

Open Scope Z_scope.
Set Default Proof Mode "Classic".

(***********************************************************)
(** Main theorem: global convergence from external acceptance *)
(***********************************************************)

Theorem Collatz_converges_from_acceptance :
  certificate_ok ->
  forall x : Z, 0 < x -> reaches_1 x.
Proof.
  intros Hok x Hxpos.
  destruct (certificate_ok_implies Hok) as [Hbd Hbr].
  (* BridgeGlobal provides the final bridge:
     bounded_descent + base_range_ok -> reaches_1 for all positive x *)
  apply (global_convergence_from_bounded_descent BASIN_CUTOFF K_bound).
  - unfold BASIN_CUTOFF; lia.
  - exact Hbd.
  - exact Hbr.
  - exact Hxpos.
Qed.
