Require Import Lists.SetoidList.
Require Import Structures.Orders Structures.OrdersFacts.

Module list_as_OT (O : OrderedType) <: OrderedType.
  (* Adapted from http://www.ensiie.fr/~robillard/Graph_Library/ *)
  Import O.
  Module Import OP := OrderedTypeFacts O.

  Definition t := list O.t.
  Definition eq := eqlistA O.eq.

  Inductive lt_ : t -> t -> Prop :=
  | ltnil : forall a l, lt_ nil (a :: l)
  | ltcons : forall a l a' l', O.lt a a' -> lt_ (a :: l) (a' :: l')
  | lt_tail : forall a a' l l', O.eq a a' -> lt_ l l' -> lt_ (a :: l) (a' :: l').

  Definition lt := lt_.

  Lemma eq_dec : forall l l', {eq l l'} + {~eq l l'}.
  Proof.
    unfold eq; induction l; intros.
    destruct l'. left. abstract intuition.
    right. abstract (intro; inversion H).
    destruct l'. right. abstract (intro; inversion H).
    destruct (IHl l').
    destruct (O.eq_dec a t0). left. abstract (constructor; auto).
    right. abstract (intro; elim n; inversion H; auto).
    right. abstract (intro; elim n; inversion H; auto).
  Defined.

  Instance eq_refl : Reflexive eq.
  Proof.
    unfold Reflexive, eq; induction x; intros. auto.
    constructor; auto. reflexivity.
  Qed.

  Instance eq_sym : Symmetric eq.
  Proof.
    unfold Symmetric, eq; induction x; intros.
    inversion H; auto.
    destruct y. inversion H.
    inversion H. subst.
    constructor; auto. symmetry. auto.
  Qed.

  Instance eq_trans : Transitive eq.
  Proof.
    unfold Transitive. induction x; unfold eq; intros.
    inversion H. subst. inversion H0. subst. auto.
    destruct y. inversion H.
    destruct z. inversion H0.
    constructor; inversion H; inversion H0; subst.
    - rewrite H4. auto.
    - rewrite H6. auto.
  Qed.

  Instance eq_equiv : Equivalence eq.
  Proof. split.
  - apply eq_refl.
  - apply eq_sym.
  - apply eq_trans.
  Qed.

  Instance lt_irrefl : Irreflexive lt.
  Proof. unfold Irreflexive, lt, Reflexive. induction x; intro.
  - inversion H.
  - inversion H; subst.
    + destruct O.lt_strorder. apply StrictOrder_Irreflexive in H1. auto.
    + contradiction.
  Qed.

  Instance lt_trans : Transitive lt.
  Proof.
    unfold Transitive. induction x; unfold lt; intros.
    inversion H; subst.
    inversion H0; subst.
    constructor.
    constructor.
    inversion H; subst.
    inversion H0; subst.
    constructor. destruct O.lt_strorder.
    apply StrictOrder_Transitive with (x := a) (y := a') (z := a'0); auto.
    inversion H0; subst.
    constructor.
    rewrite <-H3. auto.
    constructor.
    rewrite <-H3. auto.
    inversion H0; subst.
    constructor.
    rewrite H3. auto.
    apply lt_tail. rewrite H3. auto. eapply IHx; eauto.
  Qed.

  Instance lt_strorder : StrictOrder lt.
  Proof. split.
  - apply lt_irrefl.
  - apply lt_trans.
  Qed.

  Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    unfold Proper, respectful. intros a b AB. induction AB;
    intros c d CD; induction CD.
    - reflexivity.
    - split; constructor.
    - split; intros; inversion H0.
    - split; intros; inversion H1; subst.
      * apply ltcons. rewrite <- H, <- H0. auto.
      * apply lt_tail.
        -- rewrite <- H, <- H0. auto.
        -- specialize (IHAB l0 l'0 CD). apply IHAB. auto.
      * apply ltcons. rewrite H, H0. auto.
      * apply lt_tail.
        -- rewrite H, H0. auto.
        -- specialize (IHAB l0 l'0 CD). apply IHAB. auto.
  Qed.

  Fixpoint compare (l l' : t) : comparison :=
    match l, l' with
    | nil,     nil       => Eq
    | nil,     _ :: _    => Lt
    | _ :: _,  nil       => Gt
    | x :: xs, x' :: xs' =>
        match O.compare x x' with
        | Eq    => compare xs xs'
        | other => other
        end
    end.

  Theorem compare_spec : forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    induction x; destruct y.
    - apply CompEq. reflexivity.
    - apply CompLt. constructor.
    - apply CompGt. constructor.
    - simpl. destruct (O.compare_spec a t0).
      + destruct (IHx y).
        * apply CompEq. constructor; auto.
        * apply CompLt. apply lt_tail; auto.
        * apply CompGt. apply lt_tail; auto. symmetry. auto.
      + constructor. apply ltcons; auto.
      + constructor. apply ltcons; auto.
  Qed.
End list_as_OT.