From Showtime Require Import Lattice.
Require Import Classes.RelationClasses Setoid SetoidClass.
Require Vectors.Vector.
Require Import Program.Equality.

Instance JSL_Vec : forall {a n} `{JoinSemiLattice a},
                   JoinSemiLattice (Vector.t a n) := {
  join l1 l2 := Vector.map2 join l1 l2
}.

Lemma tO_is_nil_het :
  forall {a n} (v : Vector.t a n),
  n = O -> v ~= Vector.nil a.
Proof.
intros. induction v.
- auto.
- discriminate.
Qed.

Lemma tO_is_nil :
  forall {a} (v : Vector.t a O),
  v = Vector.nil a.
Proof.
intros. rewrite (tO_is_nil_het v) by auto. auto.
Qed.

Lemma tS_is_cons_het :
  forall {a n} n' (v : Vector.t a n),
  n = S n' -> exists x xs, v ~= Vector.cons a x n' xs.
Proof.
intros. induction v.
- discriminate.
- injection H as H. subst. eauto.
Qed.

Lemma tS_is_cons :
  forall {a n} (v : Vector.t a (S n)),
  exists x xs, v = Vector.cons a x n xs.
Proof.
intros. pose proof (tS_is_cons_het n v eq_refl). do 2 destruct H. rewrite H. eauto.
Qed.

Definition VecEq {a n} (rel : relation a) : Vector.t a n -> Vector.t a n -> Prop :=
  Vector.rect2 (fun _ _ _ => Prop) True (fun _ v1' v2' r x y => rel x y /\ r).

Instance VecEqReflexive :
  forall {a n} {rel : relation a} `{Reflexive a rel},
  Reflexive (@VecEq a n rel) := {}.
Proof.
  induction x.
  + constructor.
  + split.
    * reflexivity.
    * auto.
Qed.

Instance VecEqSymmetric :
  forall {a n} {rel : relation a} `{Symmetric a rel},
  Symmetric (@VecEq a n rel) := {}.
Proof.
  intros. induction x.
  + rewrite (tO_is_nil y). constructor.
  + pose proof (tS_is_cons y). do 2 destruct H1. subst.
    simpl. destruct H0. split.
    * symmetry. auto.
    * auto.
Qed.

Instance VecEqTransitive :
  forall {a n} {rel : relation a} `{Transitive a rel},
  Transitive (@VecEq a n rel) := {}.
Proof.
  intros. induction x.
  + rewrite (tO_is_nil z). constructor.
  + pose proof (tS_is_cons y). do 2 destruct H2.
    pose proof (tS_is_cons z). do 2 destruct H3. subst.
    simpl. destruct H1, H0. split.
    * rewrite H0. auto.
    * apply (IHx _ _ H3 H2).
Qed.

Instance VecEqEquivalence :
  forall {a n} {rel : relation a} `{Equivalence a rel},
  Equivalence (@VecEq a n rel) := {}.

Instance VecSetoid :
  forall {a n} `{Setoid a}, Setoid (Vector.t a n) := {
  equiv := @VecEq a n equiv
}.

Instance VJSL_Vec : forall {a n} `{VJoinSemiLattice a},
                     VJoinSemiLattice (Vector.t a n) := {}.
Proof.
- intros. induction x.
  + rewrite (tO_is_nil y), (tO_is_nil z). constructor.
  + pose proof (tS_is_cons y). do 2 destruct H0.
    pose proof (tS_is_cons z). do 2 destruct H1. subst.
    simpl. split.
    * apply (jslAssociativity h x0 x2).
    * apply IHx.
- intros. induction x.
  + rewrite (tO_is_nil y). constructor.
  + pose proof (tS_is_cons y). do 2 destruct H0. subst.
    simpl. split.
    * apply (jslCommutativity h x0).
    * apply IHx.
- intros. induction x; simpl.
  + auto.
  + split.
    * apply (jslIdempotency h).
    * apply IHx.
Qed.

Instance BJSL_Vec : forall {a n} `{BoundedJoinSemiLattice a},
                     BoundedJoinSemiLattice (Vector.t a n) := {
  bottom := Vector.const bottom n
}.

Instance VBJSL_Vec :
  forall {a n} `{VBoundedJoinSemiLattice a},
  VBoundedJoinSemiLattice (Vector.t a n) := {}.
Proof.
  intros. induction x.
  - constructor.
  - destruct H. split; auto.
Qed.