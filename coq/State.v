From Showtime Require Import Lattice Max MSet Stream Vec.
Require Import Classes.RelationClasses Setoid SetoidClass.
Require Import Lists.Streams.
Require Import MSets MSets.MSetProperties.
Require Import QArith.
Require Import Structures.Equalities Structures.Orders.

Definition Time := Max.
Definition TimeVec := Stream Time.
Definition TID := nat.
Definition Log := S.t.

CoFixpoint iterate {a : Type} (f : a -> a) (x : a) : Stream a :=
  Cons x (iterate f (f x)).

Definition naturals : Stream nat := iterate S O.

Definition epsilon : Time := mkMax 1 10.

Definition myEpsilon (n : TID) : Time :=
  MaxMult (mkMax (N.of_nat (S n)) 1) epsilon.

Inductive State : Type :=
| MkState : TimeVec -> Log -> State.

Definition StateEq (s1 s2 : State) : Prop :=
  match s1, s2 with
  | MkState t1 l1, MkState t2 l2 =>
    StreamEq MaxEq t1 t2 /\ S.Equal l1 l2
  end.

Instance StateEqReflexive : Reflexive StateEq := {}.
Proof. destruct x. split; reflexivity. Qed.

Instance StateEqSymmetric : Symmetric StateEq := {}.
Proof. destruct x, y. simpl. intros. destruct H. split; symmetry; auto. Qed.

Instance StateEqTransitive : Transitive StateEq := {}.
Proof.
  destruct x, y, z. simpl. intros. destruct H, H0. split.
  - rewrite H. auto.
  - rewrite H1. auto.
Qed.

Instance StateEqEquivalence : Equivalence StateEq := {}.

Instance StateSetoid : Setoid State := {
  equiv := StateEq
}.

Instance State_JSL : JoinSemiLattice State := {
  join s1 s2 :=
    match s1, s2 with
    | MkState t1 l1, MkState t2 l2 =>
      MkState (join t1 t2) (join l1 l2)
    end
}.

Instance State_BJSL : BoundedJoinSemiLattice State := {
  bottom := MkState (Streams.map myEpsilon naturals) S.empty
}.

Instance State_VJSL : VJoinSemiLattice State := {}.
Proof.
- destruct x, y, z. split.
  + destruct (VJSL_Stream (a := Max)). apply jslAssociativity.
  + destruct S_VJSL. apply jslAssociativity.
- destruct x, y. split.
  + destruct (VJSL_Stream (a := Max)). apply jslCommutativity.
  + destruct S_VJSL. apply jslCommutativity.
- destruct x. split.
  + destruct (VJSL_Stream (a := Max)). apply jslIdempotency.
  + destruct S_VJSL. apply jslIdempotency.
Qed.

Instance State_VBJSL : VBoundedJoinSemiLattice State := {}.
Proof.
  destruct x. split.
  - admit.
  - destruct S_VBJSL. apply bjslIdentity.
Admitted.