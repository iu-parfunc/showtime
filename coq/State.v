From QuickChick Require Import QuickChick.
From Showtime Require Import Lattice Max MMap ModuleTypes MSet Stream Vec.
Require Import Classes.RelationClasses Setoid SetoidClass.
Require Import Lists.Streams.
Require MMaps.MMapList MMaps.MMapFacts.
Require MSets.MSetAVL MSets.MSetProperties.
Require Import QArith.
Require Import Structures.Equalities Structures.Orders Structures.OrdersEx.

Module Max_Nat_as_OST := PairOrderedShowType Max_as_OST Nat_as_OST.
Module SetPairMaxNat  := MSets.MSetAVL.Make Max_Nat_as_OST.
Module VSetPairMaxNat := VMSet Max_Nat_as_OST SetPairMaxNat.
Module VMapNat2Max := VMMap Nat_as_OST Max_as_OST Max_as_OL.
Module MapNat2Max  := VMapNat2Max.M.

Definition Time := Max.
Definition TimeMap := VMapNat2Max.M'.t.
Definition TID := nat.
Definition Log := SetPairMaxNat.t.

Inductive State : Type :=
| MkState : TimeMap -> Log -> State.

Derive Show for State.

Definition StateEq (s1 s2 : State) : Prop :=
  match s1, s2 with
  | MkState t1 l1, MkState t2 l2 =>
    VMapNat2Max.M'.eq t1 t2 /\ SetPairMaxNat.Equal l1 l2
  end.

Instance StateEqReflexive : Reflexive StateEq := {}.
Proof. destruct x. split; reflexivity. Qed.

Instance StateEqSymmetric : Symmetric StateEq := {}.
Proof. destruct x, y. simpl. intros. destruct H. split; symmetry; auto. Qed.

Instance StateEqTransitive : Transitive StateEq := {}.
Proof.
  destruct x, y, z. simpl. intros. destruct H, H0. split.
  - rewrite H. auto.
  - rewrite H1. auto.
Qed.

Instance StateEqEquivalence : Equivalence StateEq := {}.

Instance StateSetoid : Setoid State := {
  equiv := StateEq
}.

Instance State_JSL : JoinSemiLattice State := {
  join s1 s2 :=
    match s1, s2 with
    | MkState t1 l1, MkState t2 l2 =>
      MkState (join t1 t2) (join l1 l2)
    end
}.

Instance State_BJSL : BoundedJoinSemiLattice State := {
  bottom := MkState bottom bottom
}.

Instance State_VJSL : VJoinSemiLattice State := {}.
Proof.
- destruct x, y, z. split.
  + destruct VMapNat2Max.VJSL. apply jslAssociativity.
  + destruct VSetPairMaxNat.VJSL. apply jslAssociativity.
- destruct x, y. split.
  + destruct VMapNat2Max.VJSL. apply jslCommutativity.
  + destruct VSetPairMaxNat.VJSL. apply jslCommutativity.
- destruct x. split.
  + destruct VMapNat2Max.VJSL. apply jslIdempotency.
  + destruct VSetPairMaxNat.VJSL. apply jslIdempotency.
Qed.

Instance State_VBJSL : VBoundedJoinSemiLattice State := {}.
Proof.
  destruct x. split.
  - destruct VMapNat2Max.VBJSL. apply bjslIdentity.
  - destruct VSetPairMaxNat.VBJSL. apply bjslIdentity.
Qed.

Module State_as_OT <: OrderedType.
  Definition t := State.

  Definition eq := StateEq.

  Instance eq_refl : Reflexive eq.
  Proof.
    unfold Reflexive. destruct x. simpl. split; reflexivity.
  Qed.

  Instance eq_sym : Symmetric eq.
  Proof.
    unfold Symmetric. destruct x, y. simpl. intro H1.
    destruct H1 as [H1 H2]. split; symmetry; auto.
  Qed.

  Instance eq_trans : Transitive eq.
  Proof.
    unfold Transitive. destruct x, y, z. simpl. intros H1 H3.
    destruct H1 as [H1 H2]. destruct H3 as [H3 H4]. split.
    - rewrite H1. auto.
    - rewrite H2. auto.
  Qed.

  Instance eq_equiv : Equivalence eq.
  Proof. split.
  - apply eq_refl.
  - apply eq_sym.
  - apply eq_trans.
  Qed.

  Theorem eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    destruct x, y. simpl.
    destruct (VMapNat2Max.eq_dec t0 t1);
    destruct (SetPairMaxNat.eq_dec l l0); auto; right; intro;
    destruct H as [H1 H2]; contradiction.
  Qed.

  Definition compare (s1 s2 : State) : comparison :=
    match s1, s2 with
    | MkState a1 b1, MkState a2 b2 =>
        match VMapNat2Max.compare a1 a2 with
        | Eq    => SetPairMaxNat.compare b1 b2
        | other => other
        end
    end.

  Inductive lt_ : t -> t -> Prop :=
  | lt_1 : forall a1 a2 b1 b2,
           VMapNat2Max.lt a1 a2 ->
           lt_ (MkState a1 b1) (MkState a2 b2)
  | lt_2 : forall a1 a2 b1 b2,
           VMapNat2Max.eq a1 a2 ->
           SetPairMaxNat.lt b1 b2 ->
           lt_ (MkState a1 b1) (MkState a2 b2).

  Definition lt := lt_.

  Instance lt_irrefl : Irreflexive lt.
  Proof.
    unfold Irreflexive, Reflexive, complement. intros.
    destruct x. inversion H; subst.
    - destruct VMapNat2Max.lt_strorder.
      apply StrictOrder_Irreflexive in H1. auto.
    - destruct SetPairMaxNat.lt_strorder.
      apply StrictOrder_Irreflexive in H5. auto.
  Qed.

  Instance lt_trans : Transitive lt.
  Proof.
    unfold Transitive. destruct x, y, z. intros.
    inversion H; inversion H0; subst.
    - apply lt_1. rewrite H2. auto.
    - apply lt_1. rewrite <- H9. auto.
    - apply lt_1. rewrite H4. auto.
    - apply lt_2.
      + rewrite H4. auto.
      + rewrite H6. auto.
  Qed.

  Instance lt_strorder : StrictOrder lt.
  Proof. split.
  - apply lt_irrefl.
  - apply lt_trans.
  Qed.

  Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    unfold Proper, respectful. destruct x, y. simpl.
    intro H1. destruct H1 as [H1 H2].
    destruct x, y. simpl.
    intro H3. destruct H3 as [H3 H4].
    split; intro Assump; inversion Assump; subst.
    - apply lt_1. rewrite <- H1, <- H3. auto.
    - apply lt_2.
      + rewrite <- H1, <- H3. auto.
      + rewrite <- H2, <- H4. auto.
    - apply lt_1. rewrite H1, H3. auto.
    - apply lt_2.
      + rewrite H1, H3. auto.
      + rewrite H2, H4. auto.
  Qed.

  Theorem compare_spec : forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    destruct x, y. simpl.
    destruct (VMapNat2Max.compare_spec t0 t1);
    try (constructor; apply lt_1; auto; fail).
    destruct (SetPairMaxNat.compare_spec l l0);
    try (constructor; apply lt_2; try (symmetry; auto; fail); auto; fail).
    constructor. auto.
  Qed.
End State_as_OT.

Module State_as_OST <: OrderedShowType.
  Include State_as_OT.
  Instance show_t : Show State := ShowState.
End State_as_OST.