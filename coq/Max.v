From Showtime Require Import Lattice.
Require Import Arith.

(* A "newtype" around nat *)
Inductive Max : Type :=
| MkMax : nat -> Max.

Instance JSL_Max : JoinSemiLattice Max := {
  join m1 m2 :=
    match m1, m2 with
    | MkMax n1, MkMax n2 => MkMax (max n1 n2)
    end
}.

Instance VJSL_Max : VJoinSemiLattice Max := {}.
Proof.
- destruct x as [n1], y as [n2], z as [n3]. simpl. rewrite Nat.max_assoc. auto.
- destruct x as [n1], y as [n2]. simpl. rewrite Nat.max_comm. auto.
- destruct x. simpl. rewrite Nat.max_id. auto.
Qed.

Instance BJSL_Max : BoundedJoinSemiLattice Max := {
  bottom := MkMax 0
}.

Instance VBJSL_Max : VBoundedJoinSemiLattice Max := {}.
Proof. destruct x. simpl. rewrite Nat.max_0_r. auto. Qed.