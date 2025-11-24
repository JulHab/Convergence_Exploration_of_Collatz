From Coq Require Import ZArith Lia Bool List.
From Collatz Require Import
  CollatzCertificate
  CertificateChecker
  CertificateData.

Open Scope Z_scope.
Import ListNotations.

(*****************************************************************)
(** 1. Bounded descent specs (boolean-aligned but decomposed)    *)
(*****************************************************************)

(* Step-level bounded descent:
   A step is “good” iff the boolean step checker passes. *)
Definition step_bounded_descent (cutoff : Z) (sc : StepCertificate) : Prop :=
  check_step cutoff sc = true.

(* Global bounded descent:
   A global certificate is “good” iff:
   - no monster was seen (negb any_monster = true),
   - every step passes [check_step],
   - deepest_depth matches max_depth via Z.eqb. *)
Definition global_bounded_descent (cutoff : Z) (gc : GlobalCertificate) : Prop :=
  negb gc.(any_monster) = true /\
  (forall sc, In sc gc.(cert_steps) -> check_step cutoff sc = true) /\
  Z.eqb gc.(deepest_depth) (max_depth gc.(cert_steps)) = true.

(* Paper hooks: Lemma 3 and Theorem 1 specialized to your concrete
   certificate and cutoff. *)
Definition Lemma3_statement : Prop :=
  global_bounded_descent BASIN_CUTOFF collatz_global_certificate.

Definition Theorem1_statement : Prop :=
  Lemma3_statement.

(*****************************************************************)
(** 2. Computational core: certificate_valid = true              *)
(*****************************************************************)

(* Heavy computation: validate the concrete global certificate. *)
Lemma certificate_valid_true :
  certificate_valid BASIN_CUTOFF collatz_global_certificate = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

(* Main theorem: same fact under a nice name. *)
Theorem collatz_consistent_with_universal_contraction :
  certificate_valid BASIN_CUTOFF collatz_global_certificate = true.
Proof.
  exact certificate_valid_true.
Qed.
