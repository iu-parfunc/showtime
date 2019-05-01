From Showtime Require Import Lattice.
Require Import Coq.Classes.RelationClasses.
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

Definition VecEq {a n} `{her : HasEquivRel a} : Vector.t a n -> Vector.t a n -> Prop :=
  Vector.rect2 (fun _ _ _ => Prop) True (fun _ v1' v2' r x y => EquivRel x y /\ r).

Instance VecHasEquivRel :
  forall {a n} `{her : HasEquivRel a},
  HasEquivRel (Vector.t a n) := {
  EquivRel := VecEq
}.

Instance VecEqEquivalence :
  forall {a n} `{vjsl : VJoinSemiLattice a},
  Equivalence (@VecEq a n her) := {}.
Proof.
- unfold Reflexive. intros. induction x.
  + constructor.
  + split.
    * destruct vjsl, er. apply Equivalence_Reflexive.
    * auto.
- unfold Symmetric. intros. induction x.
  + rewrite (tO_is_nil y). constructor.
  + pose proof (tS_is_cons y). do 2 destruct H0. subst.
    simpl. destruct H. split.
    * destruct vjsl, er. apply Equivalence_Symmetric. auto.
    * apply (IHx x1 H0).
- unfold Transitive. intros. induction x.
  + rewrite (tO_is_nil z). constructor.
  + pose proof (tS_is_cons y). do 2 destruct H1.
    pose proof (tS_is_cons z). do 2 destruct H2. subst.
    simpl. destruct H0, H. split.
    * destruct vjsl, er. apply (Equivalence_Transitive h x0 x2 H H0).
    * apply (IHx x1 x3 H2 H1).
Qed.

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