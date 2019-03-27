Class JoinSemiLattice (a : Type) := {
  join : a -> a -> a
}.
Notation "x \\// y" := (join x y) (at level 51, right associativity).

Class BoundedJoinSemiLattice a `{jsl : JoinSemiLattice a} := {
  bottom : a
}.
Notation "_|_" := (bottom).

Class VJoinSemiLattice a `{jsl : JoinSemiLattice a} := {
  jslAssociativity : forall (x y z : a),
                     (x \\// (y \\// z)) = ((x \\// y) \\// z) ;
  jslCommutativity : forall (x y : a),
                     (x \\// y) = (y \\// x) ;
  jslIdempotency : forall (x : a), (x \\// x) = x
}.

Class VBoundedJoinSemiLattice a `{bjsl : BoundedJoinSemiLattice a} := {
  bjslIdentity : forall (x : a), (x \\// _|_) = x
}.