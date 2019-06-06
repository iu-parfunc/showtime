From QuickChick Require Import QuickChick.
From Showtime Require Import Max ModuleTypes State.
Require Import Structures.Orders.

Inductive Op : Type :=
| Compute     : Time -> Op
| Open        :         Op
| BlockedOpen : Time -> Op.

Derive Show for Op.

Module Op_as_OT <: OrderedType.
  Definition t := Op.

  Inductive eq_ : t -> t -> Prop :=
  | eq_Compute : forall (t1 t2 : Time),
                 MaxEq t1 t2 -> eq_ (Compute t1) (Compute t2)
  | eq_Open : eq_ Open Open
  | eq_BlockedOpen : forall (t1 t2 : Time),
                     MaxEq t1 t2 -> eq_ (BlockedOpen t1) (BlockedOpen t2).

  Definition eq := eq_.

  Instance eq_refl : Reflexive eq.
  Proof.
    unfold Reflexive. induction x; constructor; reflexivity.
  Qed.

  Instance eq_sym : Symmetric eq.
  Proof.
    unfold Symmetric. induction x; induction y; intros; inversion H; subst;
    constructor; symmetry; auto.
  Qed.

  Instance eq_trans : Transitive eq.
  Proof.
    unfold Transitive. induction x; induction y; induction z; intros;
    inversion H; inversion H0; subst; constructor; rewrite H3; auto.
  Qed.

  Instance eq_equiv : Equivalence eq.
  Proof. split.
  - apply eq_refl.
  - apply eq_sym.
  - apply eq_trans.
  Qed.

  Theorem eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    induction x; induction y; try (right; intro; inversion H; fail).
    - destruct (Max_as_OT.eq_dec t0 t1).
      + left. constructor. auto.
      + right. intro. inversion H. auto.
    - left. constructor.
    - destruct (Max_as_OT.eq_dec t0 t1).
      + left. constructor. auto.
      + right. intro. inversion H. auto.
  Qed.

  Definition compare (o1 o2 : Op) : comparison :=
  match o1, o2 with
  | Compute t1,     Compute t2     => MaxCompare t1 t2
  | Compute _,      _              => Lt
  | Open,           Compute _      => Gt
  | Open,           Open           => Eq
  | Open,           BlockedOpen _  => Lt
  | BlockedOpen t1, BlockedOpen t2 => MaxCompare t1 t2
  | BlockedOpen _,  _              => Gt
  end.

  Inductive lt_ : t -> t -> Prop :=
  | lt_Compute_Compute : forall (t1 t2 : Time), MaxLt t1 t2 -> lt_ (Compute t1) (Compute t2)
  | lt_Compute_Open : forall (t : Time), lt_ (Compute t) Open
  | lt_Compute_BlockedOpen : forall (t1 t2 : Time), lt_ (Compute t1) (BlockedOpen t2)
  | lt_Open_BlockedOpen : forall (t : Time), lt_ Open (BlockedOpen t)
  | lt_BlockedOpen_BlockedOpen : forall (t1 t2 : Time),
                                 MaxLt t1 t2 -> lt_ (BlockedOpen t1) (BlockedOpen t2).

  Definition lt := lt_.

  Instance lt_irrefl : Irreflexive lt.
  Proof.
    unfold Irreflexive, Reflexive, complement.
    intros. induction x; inversion H;
    destruct Max_as_OT.lt_strorder;
    apply StrictOrder_Irreflexive in H2; auto.
  Qed.

  Instance lt_trans : Transitive lt.
  Proof.
    unfold Transitive. induction x; induction y; induction z; intros;
    inversion H; inversion H0; constructor;
    destruct Max_as_OT.lt_strorder;
    apply (StrictOrder_Transitive t0 t1 t2 H3 H6).
  Qed.

  Instance lt_strorder : StrictOrder lt.
  Proof. split.
  - apply lt_irrefl.
  - apply lt_trans.
  Qed.

  Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    unfold Proper, respectful.
    intros a b AB. induction AB; intros c d CD; induction CD;
    try (split; intro Assump; inversion Assump; fail);
    try (split; intro; constructor; fail).
    - split; intro Assump; inversion Assump; constructor.
      + rewrite <- H, <- H0. auto.
      + rewrite H, H0. auto.
    - split; intro Assump; inversion Assump; constructor.
      + rewrite <- H, <- H0. auto.
      + rewrite H, H0. auto.
  Qed.

  Theorem compare_spec : forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    induction x; destruct y; simpl;
    try (repeat constructor; fail);
    destruct (MaxCompareSpec t0 t1); repeat constructor; auto.
  Qed.
End Op_as_OT.

Module Op_as_OST <: OrderedShowType.
  Include Op_as_OT.
  Instance show_t : Show Op := ShowOp.
End Op_as_OST.