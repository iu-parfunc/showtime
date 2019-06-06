From QuickChick Require Import QuickChick.
From Showtime Require Import Max ModuleTypes State Op.
Require Import Structures.Orders Structures.OrdersEx.

Inductive OpInst : Type :=
| MkOpInst : TID -> Time -> Op -> OpInst.

Derive Show for OpInst.

Module OpInst_as_OT <: OrderedType.
  Definition t := OpInst.

  Definition eq_ (oi1 oi2 : OpInst) : Prop :=
    match oi1, oi2 with
    | MkOpInst a1 b1 c1, MkOpInst a2 b2 c2 =>
        Nat_as_OT.eq a1 a2 /\ Max_as_OT.eq b1 b2 /\ Op_as_OT.eq c1 c2
    end.

  Definition eq := eq_.

  Instance eq_refl : Reflexive eq.
  Proof.
    unfold Reflexive. destruct x. simpl. repeat split; reflexivity.
  Qed.

  Instance eq_sym : Symmetric eq.
  Proof.
    unfold Symmetric. destruct x, y. simpl. intro H1.
    destruct H1 as [H1 H2]. destruct H2 as [H2 H3]. repeat split; symmetry; auto.
  Qed.

  Instance eq_trans : Transitive eq.
  Proof.
    unfold Transitive. destruct x, y, z. simpl. intros H1 H4.
    destruct H1 as [H1 H2]. destruct H2 as [H2 H3].
    destruct H4 as [H4 H5]. destruct H5 as [H5 H6]. repeat split.
    - rewrite H1. auto.
    - rewrite H2. auto.
    - rewrite H3. auto.
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
    destruct (Nat_as_OT.eq_dec t0 t2);
    destruct (Max_as_OT.eq_dec t1 t3);
    destruct (Op_as_OT.eq_dec o o0); auto; right; intro;
    destruct H as [H1 H2]; destruct H2 as [H2 H3]; contradiction.
  Qed.

  Definition compare (oi1 oi2 : OpInst) : comparison :=
    match oi1, oi2 with
    | MkOpInst a1 b1 c1, MkOpInst a2 b2 c2 =>
        match Nat_as_OT.compare a1 a2 with
        | Eq =>
            match Max_as_OT.compare b1 b2 with
            | Eq => Op_as_OT.compare c1 c2
            | other => other
            end
        | other => other
        end
    end.

  Inductive lt_ : t -> t -> Prop :=
  | lt_1 : forall a1 a2 b1 b2 c1 c2,
           Nat_as_OT.lt a1 a2 ->
           lt_ (MkOpInst a1 b1 c1) (MkOpInst a2 b2 c2)
  | lt_2 : forall a1 a2 b1 b2 c1 c2,
           Nat_as_OT.eq a1 a2 ->
           Max_as_OT.lt b1 b2 ->
           lt_ (MkOpInst a1 b1 c1) (MkOpInst a2 b2 c2)
  | lt_3 : forall a1 a2 b1 b2 c1 c2,
           Nat_as_OT.eq a1 a2 ->
           Max_as_OT.eq b1 b2 ->
           Op_as_OT.lt  c1 c2 ->
           lt_ (MkOpInst a1 b1 c1) (MkOpInst a2 b2 c2).

  Definition lt := lt_.

  Instance lt_irrefl : Irreflexive lt.
  Proof.
    unfold Irreflexive, Reflexive, complement. intros.
    destruct x. inversion H; subst.
    - destruct Nat_as_OT.lt_strorder.
      apply StrictOrder_Irreflexive in H1. auto.
    - destruct Max_as_OT.lt_strorder.
      apply StrictOrder_Irreflexive in H7. auto.
    - destruct Op_as_OT.lt_strorder.
      apply StrictOrder_Irreflexive in H8. auto.
  Qed.

  Instance lt_trans : Transitive lt.
  Proof.
    unfold Transitive. destruct x, y, z. intros.
    inversion H; inversion H0; subst.
    - apply lt_1. rewrite H2. auto.
    - apply lt_1. rewrite <- H10. auto.
    - apply lt_1. rewrite <- H12. auto.
    - apply lt_1. rewrite H3. auto.
    - apply lt_2.
      + rewrite H3. auto.
      + rewrite H8. auto.
    - apply lt_2.
      + rewrite H3. auto.
      + rewrite <- H16. auto.
    - apply lt_1. rewrite H5. auto.
    - apply lt_2.
      + rewrite H5. auto.
      + rewrite H8. auto.
    - apply lt_3.
      + rewrite H5. auto.
      + rewrite H8. auto.
      + rewrite H9. auto.
  Qed.

  Instance lt_strorder : StrictOrder lt.
  Proof. split.
  - apply lt_irrefl.
  - apply lt_trans.
  Qed.

  Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    unfold Proper, respectful. destruct x, y. simpl.
    intro H1. destruct H1 as [H1 H2]. destruct H2 as [H2 H3].
    destruct x, y. simpl.
    intro H4. destruct H4 as [H4 H5]. destruct H5 as [H5 H6].
    split; intro Assump; inversion Assump; subst.
    - apply lt_1. rewrite <- H1, <- H4. auto.
    - apply lt_2.
      + rewrite <- H1, <- H4. auto.
      + rewrite <- H2, <- H5. auto.
    - apply lt_3.
      + rewrite <- H1, <- H4. auto.
      + rewrite <- H2, <- H5. auto.
      + rewrite <- H3, <- H6. auto.
    - apply lt_1. rewrite H1, H4. auto.
    - apply lt_2.
      + rewrite H1, H4. auto.
      + rewrite H2, H5. auto.
    - apply lt_3.
      + rewrite H1, H4. auto.
      + rewrite H2, H5. auto.
      + rewrite H3, H6. auto.
  Qed.

  Theorem compare_spec : forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    destruct x, y. simpl.
    destruct (Nat_as_OT.compare_spec t0 t2);
    try (constructor; apply lt_1; auto; fail).
    destruct (Max_as_OT.compare_spec t1 t3);
    try (constructor; apply lt_2; try (symmetry; auto; fail); auto; fail).
    destruct (Op_as_OT.compare_spec o o0);
    try (constructor; apply lt_3; try (symmetry; auto; fail); auto; fail).
    constructor. auto.
  Qed.
End OpInst_as_OT.

Module OpInst_as_OST <: OrderedShowType.
  Include OpInst_as_OT.
  Instance show_t : Show OpInst := ShowOpInst.
End OpInst_as_OST.