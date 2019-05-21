Require Import Classes.RelationClasses SetoidClass.
Require Import Structures.Equalities Structures.Orders.

Class JoinSemiLattice (a : Type) := {
  join : a -> a -> a
}.
Notation "x \\// y" := (join x y) (at level 51, right associativity).

Class BoundedJoinSemiLattice a `{jsl : JoinSemiLattice a} := {
  bottom : a
}.
Notation "_|_" := (bottom).

Class VJoinSemiLattice a `{jsl : JoinSemiLattice a}
                          `{s : Setoid a} := {
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

Module Type OrderedLattice (D : OrderedType).
  Declare Instance Setoid_D : Setoid D.t.
  Declare Instance JSL_D : JoinSemiLattice D.t.
  Declare Instance BJSL_D : BoundedJoinSemiLattice D.t.
  Declare Instance VJSL_D : VJoinSemiLattice D.t.
  Declare Instance VBJSL_D : VBoundedJoinSemiLattice D.t.
  Parameter dequiv_is_deq : forall (x y : D.t), SetoidClass.equiv x y = D.eq x y.
End OrderedLattice.