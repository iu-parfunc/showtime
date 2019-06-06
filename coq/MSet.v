From QuickChick Require Import Show.
From Showtime Require Import Lattice ModuleTypes.
Require Import Classes.RelationClasses SetoidClass.
Require Import MSets MSets.MSetProperties.
Require Import String.
Open Scope string_scope.

Module VMSet (X : OrderedShowType) (S : WSetsOn X).
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

  Instance show_t : Show S.t := {
    show s := "of_list " ++ show (S.elements s)
  }.
End VMSet.