From Showtime Require Import Lattice.
Require Import Classes.RelationClasses.
Require Import MSets MSets.MSetProperties.

Module S      := Make Nat_as_OT.
Module SProps := WPropertiesOn Nat_as_DT S.

Instance S_EquivRel : HasEquivRel S.t := {
  EquivRel := S.Equal
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