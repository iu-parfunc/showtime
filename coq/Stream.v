From Showtime Require Import Lattice.
Require Import Lists.Streams.
Require Import Classes.RelationClasses Setoid SetoidClass.

CoFixpoint zipWith {a b c} (f : a -> b -> c)
                    (s1 : Stream a) (s2 : Stream b) : Stream c :=
  match s1, s2 with
  | Cons x xs, Cons y ys => Cons (f x y) (zipWith f xs ys)
  end.

CoFixpoint bottoms {a} `{BoundedJoinSemiLattice a} : Stream a :=
  Cons bottom bottoms.

Instance JSL_Stream :
  forall {a} `{JoinSemiLattice a},
  JoinSemiLattice (Stream a) := {
    join := zipWith join
}.

Instance BJSL_Stream :
  forall {a} `{BoundedJoinSemiLattice a},
  BoundedJoinSemiLattice (Stream a) := {
    bottom := bottoms
}.

CoInductive StreamEq {a} (rel : relation a) (s1 s2 : Stream a) : Prop :=
| SECons : rel (hd s1) (hd s2) ->
           StreamEq rel (tl s1) (tl s2) ->
           StreamEq rel s1 s2.

Instance StreamEqReflexive :
  forall {a} {rel : relation a} `{Reflexive a rel},
  Reflexive (StreamEq rel) := {}.
Proof. cofix CIH. intros. constructor; auto. Qed.

Instance StreamEqSymmetric :
  forall {a} {rel : relation a} `{Symmetric a rel},
  Symmetric (StreamEq rel) := {}.
Proof. cofix CIH. intros. destruct H0. constructor; auto. Qed.

Instance StreamEqTransitive :
  forall {a} {rel : relation a} `{Transitive a rel},
  Transitive (StreamEq rel) := {}.
Proof.
  cofix CIH. intros. destruct H0, H1. constructor.
  - rewrite H0. apply H1.
  - apply CIH with (y := tl y); auto.
Qed.

Instance StreamEqEquivalence :
  forall {a} {rel : relation a} `{Equivalence a rel},
  Equivalence (StreamEq rel) := {}.

Instance StreamSetoid :
  forall {a} `{Setoid a}, Setoid (Stream a) := {
    equiv := StreamEq equiv
}.

Instance VJSL_Stream :
  forall {a} `{VJoinSemiLattice a},
  VJoinSemiLattice (Stream a) := {}.
Proof.
- simpl. cofix I. inversion H. destruct x, y, z. constructor; simpl; auto.
- simpl. cofix I. inversion H. destruct x, y. constructor; simpl; auto.
- simpl. cofix I. inversion H. destruct x. constructor; simpl; auto.
Qed.

Instance VBJSL_Stream :
  forall {a} `{VBoundedJoinSemiLattice a},
  VBoundedJoinSemiLattice (Stream a) := {}.
Proof.
  simpl. cofix I. inversion H. destruct x. constructor; simpl; auto.
Qed.