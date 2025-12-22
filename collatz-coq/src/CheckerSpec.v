(* CheckerSpec.v *)
From Coq Require Import ZArith String.
From Collatz Require Import BridgeGlobal.

Open Scope Z_scope.
Open Scope string_scope.
Set Default Proof Mode "Classic".

(***********************************************************)
(** Fixed run parameters                                   **)
(***********************************************************)

Definition MOD_BITS : Z := 40.
Definition MAX_DEPTH : Z := 300.
Definition BASIN_CUTOFF : Z := 1000000.
Definition K_bound : Z := 237.

(***********************************************************)
(** Pinned artifacts (hashes + counts)                      **)
(***********************************************************)

(* bucket_acceptance.json pins these *)
Definition bucket_sha256 : string :=
  "3dcf4829d932f54470f7054b81e5bcd0c032624f1d6b63378a58a18b932870be".
Definition bucket_commit_roll : string :=
  "395908b27d7f092769d860dc16aaad9fda1eab31f1831b930020dfebff19148d".
Definition bucket_commit_xor : string :=
  "6f23a8995ea6e9f4cf8569e24aa5ff8dc15f081173facdbefd92ceb772293fee".
Definition bucket_records_checked : Z := 815273437.
Definition digest_size : Z := 32.

(* coverage_report.json pins these *)
Definition total_seeds : Z := 1073741824.      (* 2^30 *)
Definition uncovered_count : Z := 274972.
Definition covered_by_bucket : Z := 1073466852.
Definition coverage_failures : Z := 0.

Definition index_sha256 : string :=
  "99308a7b6c7ac8641769675a7f90239bb825a7e20b659d4444770653ba04fcf5".
Definition uncovered_sha256 : string :=
  "2ecd2c00d4d31c57386fdb3f447f02e09185196f65d19d30135837ff3fdc1bd1".

(***********************************************************)
(** Single external acceptance hook                         **)
(***********************************************************)

(* Meaning: the external workflow was executed and the produced
   JSON reports match the pinned constants above. *)
Parameter certificate_ok : Prop.

(***********************************************************)
(** The only semantic consequence Coq may use               **)
(***********************************************************)

Axiom certificate_ok_implies :
  certificate_ok ->
  (bounded_descent BASIN_CUTOFF K_bound /\ base_range_ok BASIN_CUTOFF).
