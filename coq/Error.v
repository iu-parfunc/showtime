(* Adapted from https://github.com/antalsz/hs-to-coq/blob/b0db5644e1e7592520d5102e9d74984694766b0e/examples/base-src/manual/GHC/Err.v *)

From Showtime Require Import Max.
Require Import Strings.String.

Class Default (a : Type) := {
  default : a
}.

(* The use of [Qed] is crucial, this way we cannot look through [error] in our proofs. *)
Definition error {a} `{Default a} : string -> a.
Proof. exact (fun _ => default). Qed.

(* The use of [Qed] is crucial, this way we cannot look through [error] in our proofs. *)
Definition undefined {a} `{Default a} : a.
Proof. exact default. Qed.

Definition errorWithoutStackTrace {a} `{Default a} :
  string -> a := error.

Definition patternFailure {a} `{Default a} : a.
Proof. exact default. Qed.

Instance DefaultMax : Default Max := {
  default := MaxZero
}.