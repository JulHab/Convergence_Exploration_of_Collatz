From Coq Require Import ZArith List.

Open Scope Z_scope.

Record StepCertificate := {
  depth_c       : Z;
  a_c           : Z;
  t_c           : Z;
  A_c           : Z;
  b_c           : Z;
  n_mod_c       : Z;
  v2_last_c     : option Z;
  contract_flag : bool
}.

Record GlobalCertificate := {
  cert_steps    : list StepCertificate;
  deepest_depth : Z;
  any_monster   : bool;
  max_v2_seen   : Z
}.

