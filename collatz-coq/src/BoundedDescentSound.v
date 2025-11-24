From Coq Require Import ZArith Bool List.
From Collatz Require Import
  CollatzCertificate
  CertificateChecker
  CertificateData
  MainTheorem.

Open Scope Z_scope.
Import ListNotations.

(***********************************************************)
(** 1. Soundness of check_all_steps                        *)
(***********************************************************)

(* Purely structural: if [check_all_steps] returns true,
   then every element in the list passes [check_step]. *)
Lemma check_all_steps_sound :
  forall cutoff l,
    check_all_steps cutoff l = true ->
    forall sc, In sc l -> check_step cutoff sc = true.
Proof.
  intros cutoff l.
  induction l as [| sc0 tl IH]; intros H sc Hin.
  - (* l = [] *) inversion Hin.
  - (* l = sc0 :: tl *)
    simpl in H.
    destruct (check_step cutoff sc0) eqn:Hsc0.
    + (* head ok; tail must also be true *)
      specialize (IH H).
      simpl in Hin.
      destruct Hin as [Hin_head | Hin_tail].
      * subst sc. exact Hsc0.
      * apply IH; assumption.
    + (* head failed but overall = true ⇒ impossible *)
      discriminate H.
Qed.

(***********************************************************)
(** 2. Soundness of certificate_valid                      *)
(***********************************************************)

(* From your CertificateChecker.v we have essentially:

   Definition certificate_valid (cutoff : Z) (gc : GlobalCertificate) : bool :=
     negb gc.(any_monster)
     && check_all_steps cutoff gc.(cert_steps)
     && Z.eqb gc.(deepest_depth) (max_depth gc.(cert_steps)).

   We connect this boolean to the Prop-level
   [global_bounded_descent] from MainTheorem.v.

   IMPORTANT: we do *not* use [andb_prop] here at all; we just
   case-split on the three booleans directly.
*)

Lemma certificate_sound :
  forall cutoff gc,
    certificate_valid cutoff gc = true ->
    global_bounded_descent cutoff gc.
Proof.
  intros cutoff gc H.
  unfold certificate_valid in H.

  (* Name the three boolean components explicitly. *)
  set (b_monster := negb gc.(any_monster)).
  set (b_steps   := check_all_steps cutoff gc.(cert_steps)).
  set (b_depth   := Z.eqb gc.(deepest_depth) (max_depth gc.(cert_steps))).

  change (b_monster && b_steps && b_depth = true) in H.
  simpl in H.

  (* Case split on the three booleans; they must all be true. *)
  destruct b_monster eqn:Hmon;
    simpl in H; try discriminate.
  destruct b_steps eqn:Hsteps;
    simpl in H; try discriminate.
  destruct b_depth eqn:Hdepth;
    simpl in H; try discriminate.

  (* All three are [true]; now rebuild global_bounded_descent. *)
  unfold global_bounded_descent.
  split.
  - (* negb any_monster = true *)
    unfold b_monster in Hmon.
    (* Hmon : negb gc.(any_monster) = true *)
    exact Hmon.
  - split.
    + (* all steps satisfy step_bounded_descent *)
      intros sc Hin.
      unfold step_bounded_descent.
      unfold b_steps in Hsteps.
      (* Hsteps : check_all_steps cutoff gc.(cert_steps) = true *)
      eapply check_all_steps_sound; eauto.
    + (* deepest_depth matches max_depth via Z.eqb *)
      unfold b_depth in Hdepth.
      (* Hdepth : Z.eqb deepest_depth (max_depth ...) = true *)
      exact Hdepth.
Qed.

(***********************************************************)
(** 3. Instantiate Lemma 3 and Theorem 1 with certificate  *)
(***********************************************************)

Theorem Lemma3_from_certificate :
  Lemma3_statement.
Proof.
  unfold Lemma3_statement.
  apply (certificate_sound BASIN_CUTOFF collatz_global_certificate).
  apply certificate_valid_true.
Qed.

Theorem Theorem1_from_Lemma3 :
  Theorem1_statement.
Proof.
  unfold Theorem1_statement.
  apply Lemma3_from_certificate.
Qed.
