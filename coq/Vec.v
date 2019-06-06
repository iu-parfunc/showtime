From Showtime Require Import Lattice.
Require Import Classes.RelationClasses Setoid SetoidClass.
Require Vectors.Vector.
Import Vectors.Vector.VectorNotations.

Instance JSL_Vec : forall {a n} `{JoinSemiLattice a},
                   JoinSemiLattice (Vector.t a n) := {
  join l1 l2 := Vector.map2 join l1 l2
}.

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
  apply (Vector.rect2 (fun _ x y => VecEq rel x y -> VecEq rel y x)); simpl.
  - auto.
  - intros. destruct H1. split.
    + symmetry. auto.
    + auto.
  Qed.

Definition zip {A B} {n : nat} : Vector.t A n -> Vector.t B n -> Vector.t (A * B) n :=
  Vector.rect2 (fun n _ _ => Vector.t (A * B) n) [] (fun _ _ _ H a b => (a, b) :: H).

Definition unzip {A B} : forall {n : nat}, Vector.t (A * B) n -> (Vector.t A n * Vector.t B n) :=
  fix unzip_fix {n : nat} (v : Vector.t (A * B) n) : (Vector.t A n * Vector.t B n) :=
    match v with
    | []          => ([], [])
    | (a,b) :: v' => let (av, bv) := unzip_fix v'
                     in (a::av, b::bv)
    end.

Lemma unzip_zip :
  forall {A B n} (v1 : Vector.t A n) (v2 : Vector.t B n),
  unzip (zip v1 v2) = (v1, v2).
Proof.
  intros A B. apply Vector.rect2; simpl.
  - auto.
  - intros. rewrite H. auto.
Defined.

Definition rect3_P {A B C}
  (P : forall (n : nat), Vector.t A n -> Vector.t B n -> Vector.t C n -> Type) :
  forall (n : nat), Vector.t A n -> Vector.t (B * C) n -> Type :=
    fun n v1 v2bc =>
      let (v2b, v2c) := unzip v2bc
      in P n v1 v2b v2c.

Lemma rect3_P_zip :
  forall {A B C}
         (P : forall (n : nat), Vector.t A n -> Vector.t B n -> Vector.t C n -> Type)
         (n : nat) (v1 : Vector.t A n) (v2 : Vector.t B n) (v3 : Vector.t C n),
  P n v1 v2 v3 = rect3_P P n v1 (zip v2 v3).
Proof. intros. unfold rect3_P. rewrite unzip_zip. auto. Defined.

Lemma rect3 {A B C}
  (P : forall (n : nat), Vector.t A n -> Vector.t B n -> Vector.t C n -> Type)
  (bas : P 0 [] [] [])
  (rect : forall n v1 v2 v3, P n v1 v2 v3 ->
    forall a b c, P (S n) (a :: v1) (b :: v2) (c :: v3)) :
      forall (n : nat) (v1 : Vector.t A n) (v2 : Vector.t B n) (v3 : Vector.t C n), P n v1 v2 v3.
Proof.
  intros. rewrite rect3_P_zip. apply Vector.rect2.
  - auto.
  - unfold rect3_P. intros. destruct b. simpl.
    destruct (unzip v4). auto.
Defined.

Instance VecEqTransitive :
  forall {a n} {rel : relation a} `{Transitive a rel},
  Transitive (@VecEq a n rel) := {}.
Proof.
  apply (rect3 (fun _ x y z => VecEq rel x y -> VecEq rel y z -> VecEq rel x z)); simpl.
  - auto.
  - intros. destruct H1, H2. split.
    + rewrite H1. auto.
    + auto.
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
- revert n. apply rect3; simpl.
  + auto.
  + intros. split; auto. apply (jslAssociativity a0 b c).
- revert n. apply Vector.rect2; simpl.
  + auto.
  + intros. split; auto. apply (jslCommutativity a0 b).
- intros. induction x; simpl.
  + auto.
  + split; auto. apply (jslIdempotency h).
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