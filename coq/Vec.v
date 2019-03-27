From Showtime Require Import Lattice.
Require Vectors.Vector.
Require Import Program.Equality.

Instance JSL_Vec : forall {a n} `{JoinSemiLattice a},
                   JoinSemiLattice (Vector.t a n) := {
  join l1 l2 := Vector.map2 join l1 l2
}.

Lemma tO_is_nil_het : forall {a n} (v : Vector.t a n), n = O -> v ~= Vector.nil a.
Proof.
intros. induction v.
- auto.
- discriminate.
Qed.

Lemma tO_is_nil : forall {a} (v : Vector.t a O), v = Vector.nil a.
Proof.
intros. rewrite (tO_is_nil_het v) by auto. auto.
Qed.

Lemma tS_is_cons_het : forall {a n} n' (v : Vector.t a n), n = S n' -> exists x xs, v ~= Vector.cons a x n' xs.
Proof.
intros. induction v.
- discriminate.
- injection H as H. subst. eauto.
Qed.

Lemma tS_is_cons : forall {a n} (v : Vector.t a (S n)), exists x xs, v = Vector.cons a x n xs.
Proof.
intros. pose proof (tS_is_cons_het n v eq_refl). do 2 destruct H. rewrite H. eauto.
Qed.

Instance VJSL_Vec : forall {a n} `{VJoinSemiLattice a},
                     VJoinSemiLattice (Vector.t a n) := {}.
Proof.
- intros. induction x.
  + rewrite (tO_is_nil y), (tO_is_nil z). auto.
  + pose proof (tS_is_cons y). do 2 destruct H0.
    pose proof (tS_is_cons z). do 2 destruct H1. subst.
    simpl. rewrite (jslAssociativity h x0 x2).
    simpl in IHx. rewrite IHx. auto.
- intros. induction x.
  + rewrite (tO_is_nil y). auto.
  + pose proof (tS_is_cons y). do 2 destruct H0. subst.
    simpl. rewrite (jslCommutativity h x0).
    simpl in IHx. rewrite IHx. auto.
- intros. induction x; simpl.
  + auto.
  + rewrite (jslIdempotency h). simpl in IHx. rewrite IHx. auto.
Qed.

Instance BJSL_Vec : forall {a n} `{BoundedJoinSemiLattice a},
                     BoundedJoinSemiLattice (Vector.t a n) := {
  bottom := Vector.const _|_ n
}.

Instance VBJSL_Vec : forall {a n} `{VBoundedJoinSemiLattice a},
                      VBoundedJoinSemiLattice (Vector.t a n) := {}.
Proof.
intros. induction x.
- auto.
- simpl. rewrite (bjslIdentity h).
  simpl in IHx. rewrite IHx. auto.
Qed.