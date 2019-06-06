From QuickChick Require Import Show.
From Showtime Require Import Destruct Lattice ModuleTypes.
Require Import Omega.
Require Import QArith QArith.QOrderedType.
Require Import SetoidClass.
Require Import String.
Require Import Structures.Equalities Structures.Orders.
Open Scope string_scope.

Definition Qlt_bool (x y : Q) : bool :=
  (Qnum x * QDen y <? Qnum y * QDen x)%Z.

Lemma Qlt_alt' :
  forall {q1 q2 : Q}, (q1 < q2)%Q -> (q1 ?= q2) = Lt.
Proof.
  intros. destruct (Qlt_alt q1 q2). auto.
Qed.

Lemma Qgt_alt' :
  forall {q1 q2 : Q}, (q2 < q1)%Q -> (q1 ?= q2) = Gt.
Proof.
  intros. destruct (Qgt_alt q1 q2). auto.
Qed.

Lemma Qeq_alt' :
  forall {q1 q2 : Q}, (q1 == q2)%Q -> (q1 ?= q2) = Eq.
Proof.
  intros. destruct (Qeq_alt q1 q2). auto.
Qed.

Lemma Qltb_spec :
  forall (x y : Q), reflect (x < y)%Q (Qlt_bool x y).
Proof.
  intros. unfold Qlt_bool, Z.ltb.
  destruct (Qcompare x y) eqn:Z; unfold Qcompare in Z; rewrite Z; constructor; auto;
  intro; unfold Qlt in H; unfold Z.lt in H; rewrite H in Z; discriminate.
Qed.

Lemma Qleb_spec :
  forall (x y : Q), reflect (x <= y)%Q (Qle_bool x y).
Proof.
  intros. unfold Qle_bool, Z.leb.
  destruct (Qcompare x y) eqn:Z; unfold Qcompare in Z; rewrite Z; constructor; auto;
  unfold Qle, Z.le; intro; rewrite H in Z; discriminate.
Qed.

Lemma Qeqb_spec :
  forall (x y : Q), reflect (x == y)%Q (Qeq_bool x y).
Proof.
  intros. destruct (Q_as_DT.eq_dec x y).
  - rewrite (Qeq_eq_bool x y q). constructor. auto.
  - destruct (not_iff_compat (Qeq_bool_iff x y)).
    rewrite (not_true_is_false (Qeq_bool x y) (H0 n)).
    constructor. auto.
Qed.

Hint Resolve Qltb_spec Qleb_spec Qeqb_spec : bdestruct.
Hint Resolve Qcompare_spec : cdestruct.

(* A "newtype" around Q *)
Inductive Max : Type :=
| MkMax : forall (q : Q), (0 <= Qnum q)%Z -> Max.

Instance showPos : Show positive := {
  show p := show (Pos.to_nat p)
}.

Instance showQ : Show Q := {
  show q := match Qred q with
            | Qmake n d => show n ++ " / " ++ show d
            end
}.

Instance showMax : Show Max := {
  show m := match m with
            | MkMax q _ => show q
            end
}.

Lemma ZofNNonNeg :
  forall (numer : N), (0 <= Z.of_N numer)%Z.
Proof.
  destruct numer; simpl.
  - reflexivity.
  - apply Zle_0_pos.
Qed.

Lemma ZofNatNonNeg :
  forall (numer : nat), (0 <= Z.of_nat numer)%Z.
Proof.
  destruct numer; simpl.
  - reflexivity.
  - apply Zle_0_pos.
Qed.

Definition mkMaxN (numer : N) (denom : positive) : Max :=
  MkMax (Qmake (Z.of_N numer) denom) (ZofNNonNeg numer).

Definition N_to_Max (n : N) : Max := mkMaxN n 1.

Definition mkMaxNat (numer : nat) (denom : positive) : Max :=
  MkMax (Qmake (Z.of_nat numer) denom) (ZofNatNonNeg numer).

Definition nat_to_Max (n : nat) : Max := mkMaxNat n 1.

Definition MaxEq (m1 m2 : Max) : Prop :=
  match m1, m2 with
  | MkMax q1 _, MkMax q2 _ => Qeq q1 q2
  end.

Notation "m1 === m2" := (MaxEq m1 m2) (at level 70).

Definition MaxEqb (m1 m2 : Max) : bool :=
  match m1, m2 with
  | MkMax q1 _, MkMax q2 _ => Qeq_bool q1 q2
  end.

Definition MaxLt (m1 m2 : Max) : Prop :=
  match m1, m2 with
  | MkMax q1 _, MkMax q2 _ => Qlt q1 q2
  end.

Notation "m1 < m2" := (MaxLt m1 m2) (at level 70).

Definition MaxLtb (m1 m2 : Max) : bool :=
  match m1, m2 with
  | MkMax q1 _, MkMax q2 _ => Qlt_bool q1 q2
  end.

Notation "m1 <? m2" := (MaxLtb m1 m2) (at level 70).

Definition MaxLe (m1 m2 : Max) : Prop :=
  match m1, m2 with
  | MkMax q1 _, MkMax q2 _ => Qle q1 q2
  end.

Notation "m1 <= m2" := (MaxLe m1 m2) (at level 70).

Definition MaxLeb (m1 m2 : Max) : bool :=
  match m1, m2 with
  | MkMax q1 _, MkMax q2 _ => Qle_bool q1 q2
  end.

Notation "m1 <=? m2" := (MaxLeb m1 m2) (at level 70).

Definition MaxGt (m1 m2 : Max) : Prop := MaxLt m2 m1.

Notation "m1 > m2" := (MaxGt m1 m2) (at level 70).

Definition MaxGtb (m1 m2 : Max) : bool := MaxLtb m2 m1.

Notation "m1 >? m2" := (MaxGtb m1 m2) (at level 70).

Definition MaxGeb (m1 m2 : Max) : bool := MaxLeb m2 m1.

Notation "m1 >=? m2" := (MaxGeb m1 m2) (at level 70).

Definition MaxCompare (m1 m2 : Max) : comparison :=
  match m1, m2 with
  | MkMax q1 _, MkMax q2 _ => Qcompare q1 q2
  end.

Definition max (m1 m2 : Max) : Max :=
  match m1, m2 with
  | MkMax q1 _, MkMax q2 _ =>
    match Qcompare q1 q2 with
    | Gt => m1
    | _  => m2
    end
  end.

Definition min (m1 m2 : Max) : Max :=
  match m1, m2 with
  | MkMax q1 _, MkMax q2 _ =>
    match Qcompare q1 q2 with
    | Lt => m1
    | _  => m2
    end
  end.

Lemma maxMultNonNeg :
  forall (q1 q2 : Q),
  (0 <= Qnum q1)%Z -> (0 <= Qnum q2)%Z -> (0 <= Qnum (q1 * q2))%Z.
Proof.
  destruct q1, q2. simpl. intros.
  destruct Qnum; destruct Qnum0; simpl; try contradiction; try omega; try (apply Zle_0_pos).
Qed.

Lemma maxAddNonNeg :
  forall (q1 q2 : Q),
  (0 <= Qnum q1)%Z -> (0 <= Qnum q2)%Z -> (0 <= Qnum (q1 + q2))%Z.
Proof.
  destruct q1, q2. simpl. intros.
  destruct Qnum; destruct Qnum0; simpl; try contradiction; try omega; try (apply Zle_0_pos).
Qed.

Definition MaxAdd (m1 m2 : Max) : Max :=
  match m1, m2 with
  | MkMax q1 q1NonNeg, MkMax q2 q2NonNeg =>
    MkMax (q1 + q2) (maxAddNonNeg q1 q2 q1NonNeg q2NonNeg)
  end.

Notation "m1 + m2" := (MaxAdd m1 m2) (at level 50, left associativity).

(* Zeroes if the subtrahend is larger than the minuend. *)
Definition Qminus_pos (q1 q2 : Q) : Q :=
  match Qcompare q1 q2 with
  | Lt => 0
  | _  => Qminus q1 q2
  end.

Lemma maxMinusNonNeg :
  forall (q1 q2 : Q),
  (0 <= Qnum q1)%Z -> (0 <= Qnum q2)%Z -> (0 <= Qnum (Qminus_pos q1 q2))%Z.
Proof.
  destruct q1, q2. simpl. intros.
  destruct Qnum; destruct Qnum0; simpl; try contradiction; try omega.
  - apply Zle_0_pos.
  - unfold Qminus_pos. cdestruct (Z.pos p # Qden ?= Z.pos p0 # Qden0)%Q.
    * simpl. unfold Qeq in H1. simpl in H1. injection H1 as X. rewrite X.
      rewrite Z.pos_sub_diag. reflexivity.
    * reflexivity.
    * simpl. unfold Qeq in H1. unfold Qlt in H1. simpl in H1.
      rewrite Z.pos_sub_gt; auto.
Qed.

(* Zeroes if the subtrahend is larger than the minuend. *)
Definition MaxMinus (m1 m2 : Max) : Max :=
  match m1, m2 with
  | MkMax q1 q1NonNeg, MkMax q2 q2NonNeg =>
    MkMax (Qminus_pos q1 q2) (maxMinusNonNeg q1 q2 q1NonNeg q2NonNeg)
  end.

Notation "m1 - m2" := (MaxMinus m1 m2) (at level 50, left associativity).

Definition MaxMult (m1 m2 : Max) : Max :=
  match m1, m2 with
  | MkMax q1 q1NonNeg, MkMax q2 q2NonNeg =>
    MkMax (q1 * q2) (maxMultNonNeg q1 q2 q1NonNeg q2NonNeg)
  end.

Notation "m1 * m2" := (MaxMult m1 m2) (at level 40, left associativity).

Definition MaxZero : Max := nat_to_Max 0.

Ltac rewrite_Qeqs :=
  repeat match goal with
  | H : (?q1 <  ?q2)%Q |- context[?q1 ?= ?q2] => rewrite (Qlt_alt' H)
  | H : (?q1 <  ?q2)%Q |- context[?q2 ?= ?q1] => rewrite (Qgt_alt' H)
  | H : (?q1 == ?q2)%Q |- context[?q1 ?= ?q2] => rewrite (Qeq_alt' H)
  | H : (?q1 == ?q2)%Q |- context[?q2 ?= ?q1] => rewrite (Qeq_alt' (eq_sym H))
  | |- context[?q ?= ?q] => rewrite (Qeq_alt' (Qeq_refl q))
  end.

Ltac crush_Q :=
  simpl; rewrite_Qeqs; simpl; q_order.

Lemma Qlt_0_neg :
  forall (q : Q), (q < 0)%Q -> (Qnum q < 0)%Z.
Proof.
  intros. destruct q. simpl. destruct Qnum; auto.
Qed.

Theorem max_associative :
  forall (m1 m2 m3 : Max), MaxEq (max m1 (max m2 m3)) (max (max m1 m2) m3).
Proof.
  destruct m1 as [q1]. destruct m2 as [q2]. destruct m3 as [q3]. simpl.
  cdestruct (q1 ?= q2); cdestruct (q2 ?= q3); cdestruct (q1 ?= q3); crush_Q.
Qed.

Theorem max_commutative :
  forall (m1 m2 : Max), MaxEq (max m1 m2) (max m2 m1).
Proof.
  destruct m1, m2. simpl.
  cdestruct (q ?= q0); cdestruct (q0 ?= q); crush_Q.
Qed.

Theorem max_idempotent :
  forall (m : Max), MaxEq (max m m) m.
Proof.
  destruct m. crush_Q.
Qed.

Theorem max_identity :
  forall (m : Max), MaxEq (max m MaxZero) m.
Proof.
  destruct m. simpl. cdestruct (q ?= 0); try crush_Q.
  apply Qlt_0_neg in H. omega.
Qed.

Instance jslMax : JoinSemiLattice Max := {
  join := max
}.

Instance bjslMax : BoundedJoinSemiLattice Max := {
  bottom := MaxZero
}.

Instance maxEqReflexive : Reflexive MaxEq := {}.
Proof. destruct x. crush_Q. Qed.

Instance maxEqSymmetric : Symmetric MaxEq := {}.
Proof. destruct x, y. crush_Q. Qed.

Instance maxEqTransitive : Transitive MaxEq := {}.
Proof. destruct x, y, z. crush_Q. Qed.

Instance maxEqEquivalence : Equivalence MaxEq := {}.

Instance maxEqSetoid : Setoid Max := {
  equiv := MaxEq
}.

Instance maxLtTransitive : Transitive MaxLt := {}.
Proof. destruct x, y, z. crush_Q. Qed.

Instance maxLtIrreflexive : Irreflexive MaxLt := {}.
Proof. unfold Reflexive. destruct x. unfold complement. crush_Q. Qed.

Instance maxLtStrictOrder : StrictOrder MaxLt := {}.

Instance vjslMax : VJoinSemiLattice Max := {
  jslAssociativity := max_associative
; jslCommutativity := max_commutative
; jslIdempotency   := max_idempotent
}.

Instance vbjslMax : VBoundedJoinSemiLattice Max := {
  bjslIdentity := max_identity
}.

Module Max_as_DT <: DecidableType.
  Definition t := Max.

  Definition eq := MaxEq.

  Instance eq_refl : Reflexive eq := maxEqReflexive.

  Instance eq_sym : Symmetric eq := maxEqSymmetric.

  Instance eq_trans : Transitive eq := maxEqTransitive.

  Instance eq_equiv : Equivalence eq := maxEqEquivalence.

  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof. destruct x, y. apply Q_as_DT.eq_dec. Qed.
End Max_as_DT.

Module Max_as_OT <: OrderedType.
  Include Max_as_DT.

  Definition lt := MaxLt.

  Instance lt_strorder : StrictOrder lt := maxLtStrictOrder.

  Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    unfold Proper, respectful. destruct x, y. simpl.
    destruct x, y. simpl. intros. split; crush_Q.
  Qed.

  Definition compare := MaxCompare.

  Lemma compare_spec : forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof. destruct x, y. simpl. cdestruct (q ?= q0); auto. Qed.
End Max_as_OT.

Module Max_as_OST <: OrderedShowType.
  Include Max_as_OT.
  Instance show_t : Show Max := showMax.
End Max_as_OST.

Module Max_as_OL <: OrderedLattice Max_as_OT.
  Instance Setoid_D : Setoid Max := maxEqSetoid.
  Instance JSL_D : JoinSemiLattice Max := jslMax.
  Instance BJSL_D : BoundedJoinSemiLattice Max := bjslMax.
  Instance VJSL_D : VJoinSemiLattice Max := vjslMax.
  Instance VBJSL_D : VBoundedJoinSemiLattice Max := vbjslMax.
  Theorem dequiv_is_deq : forall x y, equiv x y = MaxEq x y. Proof. auto. Qed.
End Max_as_OL.

Definition MaxLtbSpec :
  forall (x y : Max), reflect (x < y) (x <? y).
Proof. destruct x, y. apply Qltb_spec. Qed.

Definition MaxLeqSpec :
  forall (x y : Max), reflect (x <= y) (x <=? y).
Proof. destruct x, y. apply Qleb_spec. Qed.

Definition MaxEqSpec :
  forall (x y : Max), reflect (x === y) (MaxEqb x y).
Proof. destruct x, y. apply Qeqb_spec. Qed.

Hint Resolve MaxLtbSpec MaxLeqSpec MaxEqSpec : bdestruct.

Definition MaxCompareSpec :
  forall (x y : Max), CompareSpec (x === y) (x < y) (y < x) (MaxCompare x y).
Proof. apply Max_as_OT.compare_spec. Qed.

Hint Resolve MaxCompareSpec : cdestruct.