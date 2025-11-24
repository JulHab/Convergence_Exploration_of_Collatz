From Coq Require Import List ZArith Bool Lia.
From Collatz Require Import CollatzCertificate.

Open Scope Z_scope.
Import ListNotations.

(* Maximale Tiefe über alle Steps *)
Fixpoint max_depth (l : list StepCertificate) : Z :=
  match l with
  | [] => 0%Z
  | sc :: tl => Z.max sc.(depth_c) (max_depth tl)
  end.

(* Einzelnen Step prüfen:

   - A_c = 3^a_c
   - contract_flag entspricht (delta > 0)
   - falls delta > 0: b_c < cutoff * delta
*)
Definition check_step (cutoff : Z) (sc : StepCertificate) : bool :=
  let A_expected := (3 ^ sc.(a_c))%Z in
  let two_t      := (2 ^ sc.(t_c))%Z in
  let delta      := (two_t - sc.(A_c))%Z in
  let has_contract := Z.gtb delta 0 in
  let ok_A         := Z.eqb sc.(A_c) A_expected in
  let ok_flag      := Bool.eqb has_contract sc.(contract_flag) in
  let ok_b :=
    if has_contract
    then Z.ltb sc.(b_c) (cutoff * delta)
    else true
  in
  ok_A && ok_flag && ok_b.

Fixpoint check_all_steps (cutoff : Z) (l : list StepCertificate) : bool :=
  match l with
  | [] => true
  | sc :: tl =>
      if check_step cutoff sc
      then check_all_steps cutoff tl
      else false
  end.

Definition certificate_valid (cutoff : Z) (gc : GlobalCertificate) : bool :=
  negb gc.(any_monster)
  && check_all_steps cutoff gc.(cert_steps)
  && Z.eqb gc.(deepest_depth) (max_depth gc.(cert_steps)).
