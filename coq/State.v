From Showtime Require Import Lattice Max MMap MSet Stream Vec.
Require Import Classes.RelationClasses Setoid SetoidClass.
Require Import Lists.Streams.
Require MMaps.MMapList MMaps.MMapFacts.
Require MSets.MSetAVL MSets.MSetProperties.
Require Import QArith.
Require Import Structures.Equalities Structures.Orders Structures.OrdersEx.

Module Max_Nat_as_OT := PairOrderedType Max_as_OT Nat_as_OT.
Module S  := MSets.MSetAVL.Make Max_Nat_as_OT.
Module VS := VMSet Max_Nat_as_OT S.
Module VM := VMMap Nat_as_OT Max_as_OT Max_as_OL.
Module M  := VM.M.

Definition Time := Max.
Definition TimeMap := M.t.
Definition TID := nat.
Definition Log := S.t.

Inductive State : Type :=
| MkState : TimeMap -> Log -> State.

Definition StateEq (s1 s2 : State) : Prop :=
  match s1, s2 with
  | MkState t1 l1, MkState t2 l2 =>
    M.eq t1 t2 /\ S.Equal l1 l2
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
  bottom := MkState bottom bottom
}.

Instance State_VJSL : VJoinSemiLattice State := {}.
Proof.
- destruct x, y, z. split.
  + destruct VM.VJSL. apply jslAssociativity.
  + destruct VS.VJSL. apply jslAssociativity.
- destruct x, y. split.
  + destruct VM.VJSL. apply jslCommutativity.
  + destruct VS.VJSL. apply jslCommutativity.
- destruct x. split.
  + destruct VM.VJSL. apply jslIdempotency.
  + destruct VS.VJSL. apply jslIdempotency.
Qed.

Instance State_VBJSL : VBoundedJoinSemiLattice State := {}.
Proof.
  destruct x. split.
  - destruct VM.VBJSL. apply bjslIdentity.
  - destruct VS.VBJSL. apply bjslIdentity.
Qed.