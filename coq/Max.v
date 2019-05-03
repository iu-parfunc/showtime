From Showtime Require Import Lattice.
Require Import Omega.
Require Import QArith.

(* A "newtype" around Q *)
Inductive Max : Type :=
| MkMax : forall (q : Q), (0 <= Qnum q)%Z -> Max.

Definition MaxEq (m1 m2 : Max) : Prop :=
  match m1, m2 with
  | MkMax q1 _, MkMax q2 _ => Qeq q1 q2
  end.

Definition max (m1 m2 : Max) : Max :=
  match m1, m2 with
  | MkMax q1 _, MkMax q2 _ =>
    match Qcompare q1 q2 with
    | Gt => m1
    | _  => m2
    end
  end.

Definition zero : Max := MkMax 0 (Z.le_refl 0).

Lemma Qcompare_no_converse :
  forall {q1 q2 : Q}, q1 < q2 -> ~ (q2 < q1).
Proof.
  intros. intro. rewrite Qlt_alt in H. rewrite Qgt_alt in H0.
  rewrite H in H0. discriminate.
Qed.

Lemma Qlt_alt' :
  forall {q1 q2 : Q}, q1 < q2 -> (q1 ?= q2) = Lt.
Proof.
  intros. destruct (Qlt_alt q1 q2). auto.
Qed.

Lemma Qgt_alt' :
  forall {q1 q2 : Q}, q2 < q1 -> (q1 ?= q2) = Gt.
Proof.
  intros. destruct (Qgt_alt q1 q2). auto.
Qed.

Lemma Qeq_alt' :
  forall {q1 q2 : Q}, q1 == q2 -> (q1 ?= q2) = Eq.
Proof.
  intros. destruct (Qeq_alt q1 q2). auto.
Qed.

Hint Resolve Qcompare_spec : cdestruct.

Ltac cdestruct X :=
  let H := fresh in let e1 := fresh "e1" in let e2 := fresh "e2" in let e3 := fresh "e3" in
   evar (e1: Prop); evar (e2: Prop); evar (e3: Prop);
   assert (H: CompareSpec e1 e2 e3 X); subst e1; subst e2; subst e3;
    [eauto with cdestruct
    | destruct H as [H|H|H] ].

Ltac crush_Qcompare :=
  repeat match goal with
  | H : ?q1 <  ?q2 |- context[?q1 ?= ?q2] => rewrite (Qlt_alt' H)
  | H : ?q1 <  ?q2 |- context[?q2 ?= ?q1] => rewrite (Qgt_alt' H)
  | H : ?q1 == ?q2 |- context[?q1 ?= ?q2] => rewrite (Qeq_alt' H)
  | H : ?q1 == ?q2 |- context[?q2 ?= ?q1] => rewrite (Qeq_alt' (eq_sym H))
  | |- context[?q ?= ?q] => rewrite (Qeq_alt' (Qeq_refl q))
  | |- ?q == ?q => apply Qeq_refl
  | H : ?q1 == ?q2 |- ?q2 == ?q1 => apply (Qeq_sym q1 q2 H)
  | H1 : ?q1 == ?q2, H2 : ?q2 == ?q3 |- ?q1 == ?q3 => apply (Qeq_trans q1 q2 q3 H1 H2)
  | H1 : ?q1 < ?q2, H2 : ?q2 < ?q1 |- _ => destruct (Qcompare_no_converse H1 H2)
  | |- _ => assumption
  end.

Lemma Qlt_0_neg :
  forall (q : Q), q < 0 -> (Qnum q < 0)%Z.
Proof.
  intros. destruct q. simpl. destruct Qnum; auto.
Qed.

Theorem max_associative :
  forall (m1 m2 m3 : Max), MaxEq (max m1 (max m2 m3)) (max (max m1 m2) m3).
Proof.
  destruct m1 as [q1]. destruct m2 as [q2]. destruct m3 as [q3]. simpl.
  cdestruct (q1 ?= q2); cdestruct (q2 ?= q3); cdestruct (q1 ?= q3);
  repeat (simpl; crush_Qcompare).
  - rewrite <- H in H0. crush_Qcompare.
  - rewrite H0 in H. crush_Qcompare.
  - pose proof (Qlt_trans q1 q2 q3 H H0). crush_Qcompare.
  - pose proof (Qlt_trans q1 q3 q2 H1 H0). crush_Qcompare.
Qed.

Theorem max_commutative :
  forall (m1 m2 : Max), MaxEq (max m1 m2) (max m2 m1).
Proof.
  destruct m1, m2. simpl.
  cdestruct (q ?= q0); cdestruct (q0 ?= q); repeat (simpl; crush_Qcompare).
Qed.

Theorem max_idempotent :
  forall (m : Max), MaxEq (max m m) m.
Proof.
  destruct m. repeat (simpl; crush_Qcompare).
Qed.

Theorem max_identity :
  forall (m : Max), MaxEq (max m zero) m.
Proof.
  destruct m. simpl. cdestruct (q ?= 0); simpl; crush_Qcompare.
  apply Qlt_0_neg in H. omega.
Qed.

Instance jslMax : JoinSemiLattice Max := {
  join := max
}.

Instance bjslMax : BoundedJoinSemiLattice Max := {
  bottom := zero
}.

Instance hasEquivRelMax : HasEquivRel Max := {
  EquivRel := MaxEq
}.

Instance maxEqEquivalence : Equivalence MaxEq := {}.
Proof.
- unfold Reflexive. destruct x. simpl. crush_Qcompare.
- unfold Symmetric. destruct x, y. simpl. intros. crush_Qcompare.
- unfold Transitive. destruct x, y, z. simpl. intros. crush_Qcompare.
Qed.

Instance vjslMax : VJoinSemiLattice Max := {
  jslAssociativity := max_associative
; jslCommutativity := max_commutative
; jslIdempotency   := max_idempotent
}.

Instance vbjslMax : VBoundedJoinSemiLattice Max := {
  bjslIdentity := max_identity
}.