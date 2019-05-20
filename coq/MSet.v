From Showtime Require Import Lattice.
Require Import Classes.RelationClasses SetoidClass.
Require Import MSets MSets.MSetProperties.

Module VMSet (X : OrderedType) (S : WSetsOn X).
  Module SProps := WPropertiesOn X S.

  Instance Setoid : Setoid S.t := {
    equiv := S.Equal
  }.

  Instance JSL : JoinSemiLattice S.t := {
    join := S.union
  }.

  Instance BJSL : BoundedJoinSemiLattice S.t := {
    bottom := S.empty
  }.

  Instance VJSL : VJoinSemiLattice S.t := {}.
  Proof.
  - intros. simpl. symmetry. apply SProps.union_assoc.
  - intros. simpl. apply SProps.union_sym.
  - intros. simpl. apply SProps.union_subset_equal. reflexivity.
  Qed.

  Instance VBJSL : VBoundedJoinSemiLattice S.t := {}.
  Proof.
    intros. simpl. apply SProps.empty_union_2. apply S.empty_spec.
  Qed.
End VMSet.