From Showtime Require Import Lattice Max.
Require Import Classes.RelationClasses SetoidClass.
Require Import MSets MSets.MSetProperties.

Module Max_Nat_as_OT := PairOrderedType Max_as_OT Nat_as_OT.
Module S      := Make Max_Nat_as_OT.
Module SProps := WPropertiesOn Max_Nat_as_OT S.

Instance S_Setoid : Setoid S.t := {
  equiv := S.Equal
}.

Instance S_JSL : JoinSemiLattice S.t := {
  join := S.union
}.

Instance S_BJSL : BoundedJoinSemiLattice S.t := {
  bottom := S.empty
}.

Instance S_VJSL : VJoinSemiLattice S.t := {}.
Proof.
- intros. simpl. symmetry. apply SProps.union_assoc.
- intros. simpl. apply SProps.union_sym.
- intros. simpl. apply SProps.union_subset_equal. reflexivity.
Qed.

Instance S_VBJSL : VBoundedJoinSemiLattice S.t := {}.
Proof.
  intros. simpl. apply SProps.empty_union_2. auto.
Qed.