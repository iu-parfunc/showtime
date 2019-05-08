Require Import Classes.RelationClasses SetoidClass.

Class JoinSemiLattice (a : Type) := {
  join : a -> a -> a
}.
Notation "x \\// y" := (join x y) (at level 51, right associativity).

Class BoundedJoinSemiLattice a `{jsl : JoinSemiLattice a} := {
  bottom : a
}.
Notation "_|_" := (bottom).

Class VJoinSemiLattice a `{jsl : JoinSemiLattice a}
                          `{s : Setoid a}
                          (*
                          `{her : HasEquivRel a}
                          `{er : Equivalence a (@EquivRel a her)} *) := {
  jslAssociativity : forall (x y z : a),
                     (x \\// (y \\// z)) == ((x \\// y) \\// z)
; jslCommutativity : forall (x y : a),
                     (x \\// y) == (y \\// x)
; jslIdempotency : forall (x : a), (x \\// x) == x
}.

Class VBoundedJoinSemiLattice a
  `{s : Setoid a}
  `{bjsl : BoundedJoinSemiLattice a}
  `{vjsl : ! VJoinSemiLattice a} := {
  bjslIdentity : forall (x : a), (x \\// _|_) == x
}.