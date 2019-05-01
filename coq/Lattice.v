Require Import Coq.Classes.RelationClasses.

Class HasEquivRel (a : Type) := {
  EquivRel : a -> a -> Prop
}.
Notation "x =~= y" := (EquivRel x y) (at level 90).

Class JoinSemiLattice (a : Type) := {
  join : a -> a -> a
}.
Notation "x \\// y" := (join x y) (at level 51, right associativity).

Class BoundedJoinSemiLattice a `{jsl : JoinSemiLattice a} := {
  bottom : a
}.
Notation "_|_" := (bottom).

Class VJoinSemiLattice a `{jsl : JoinSemiLattice a}
                          `{her : HasEquivRel a}
                          `{er : Equivalence a (@EquivRel a her)} := {
  jslAssociativity : forall (x y z : a),
                     (x \\// (y \\// z)) =~= ((x \\// y) \\// z)
; jslCommutativity : forall (x y : a),
                     (x \\// y) =~= (y \\// x)
; jslIdempotency : forall (x : a), (x \\// x) =~= x
}.

Class VBoundedJoinSemiLattice a
  `{her : HasEquivRel a}
  `{er : Equivalence a (@EquivRel a her)}
  `{bjsl : BoundedJoinSemiLattice a}
  `{vjsl : ! VJoinSemiLattice a} := {
  bjslIdentity : forall (x : a), (x \\// _|_) =~= x
}.