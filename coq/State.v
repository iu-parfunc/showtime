From Showtime Require Import Lattice Max MMap MSet Stream Vec.
Require Import Classes.RelationClasses Setoid SetoidClass.
Require Import Lists.Streams.
Require MMaps.MMapList MMaps.MMapFacts.
Require MSets.MSetAVL MSets.MSetProperties.
Require Import QArith.
Require Import Structures.Equalities Structures.Orders Structures.OrdersEx.

Module Max_Nat_as_OT := PairOrderedType Max_as_OT Nat_as_OT.
Module SetPairMaxNat  := MSets.MSetAVL.Make Max_Nat_as_OT.
Module VSetPairMaxNat := VMSet Max_Nat_as_OT SetPairMaxNat.
Module VMapNat2Max := VMMap Nat_as_OT Max_as_OT Max_as_OL.
Module MapNat2Max  := VMapNat2Max.M.

Definition Time := Max.
Definition TimeMap := VMapNat2Max.M'.t.
Definition TID := nat.
Definition Log := SetPairMaxNat.t.

Inductive State : Type :=
| MkState : TimeMap -> Log -> State.

Definition StateEq (s1 s2 : State) : Prop :=
  match s1, s2 with
  | MkState t1 l1, MkState t2 l2 =>
    VMapNat2Max.M'.eq t1 t2 /\ SetPairMaxNat.Equal l1 l2
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
  + destruct VMapNat2Max.VJSL. apply jslAssociativity.
  + destruct VSetPairMaxNat.VJSL. apply jslAssociativity.
- destruct x, y. split.
  + destruct VMapNat2Max.VJSL. apply jslCommutativity.
  + destruct VSetPairMaxNat.VJSL. apply jslCommutativity.
- destruct x. split.
  + destruct VMapNat2Max.VJSL. apply jslIdempotency.
  + destruct VSetPairMaxNat.VJSL. apply jslIdempotency.
Qed.

Instance State_VBJSL : VBoundedJoinSemiLattice State := {}.
Proof.
  destruct x. split.
  - destruct VMapNat2Max.VBJSL. apply bjslIdentity.
  - destruct VSetPairMaxNat.VBJSL. apply bjslIdentity.
Qed.