From QuickChick Require Import Show.
From Showtime Require Import Destruct Lattice ModuleTypes.
Require Import Classes.RelationClasses.
Require Import MMaps.MMapList MMaps.MMapFacts.
Require Import String.
Require SetoidClass. (* (==) from SetoidClass clashes with stuff from MMaps. Ugh. *)
Module SC := SetoidClass.
Open Scope string_scope.

Module VMMap (X : OrderedShowType) (D : OrderedShowType) (Import P: OrderedLattice D)
    <: OrderedType.
  Module M'     := Make_ord X D.
  Module M      := M'.MapS.
  Module MProps := WProperties_fun X M.
  Include M'.

  (* Useful tactics *)

  Hint Resolve X.compare_spec D.compare_spec : cdestruct.

  (* Let's make it a DecidableType *)

  Theorem eq_dec : forall (x y : M.t D.t), { eq x y } + { ~ eq x y }.
  Proof.
    intros.
    destruct (eq_equal x y) as [X Y].
    destruct (M.equal cmp x y) eqn:H.
    - left. apply Y. auto.
    - right. intro. specialize (X H0). discriminate.
  Qed.

  (* Some useful auxiliary definitions *)

  Definition raw_adjusti (f : X.t -> D.t -> D.t) (k : X.t)
      : M.Raw.t D.t -> M.Raw.t D.t :=
    fix go (m : M.Raw.t D.t) : M.Raw.t D.t :=
      match m with
      | nil => nil
      | (kx, x) :: xs =>
          match X.compare k kx with
          | Eq => (kx, f kx x) :: xs
          | _  => (kx,      x) :: go xs
          end
      end.

  Definition raw_adjust (f : D.t -> D.t)
      : X.t -> M.Raw.t D.t -> M.Raw.t D.t :=
    raw_adjusti (fun _ x => f x).

  Lemma adjusti_HdRel :
    forall (f : X.t -> D.t -> D.t) (k1 k2 : X.t) (v : D.t) (m : M.Raw.t D.t),
    HdRel M.Raw.PX.ltk (k1, v) m -> HdRel M.Raw.PX.ltk (k1, v) (raw_adjusti f k2 m).
  Proof.
    intros. induction H; simpl; auto.
    destruct b. cdestruct (X.compare k2 t0); auto.
  Qed.

  Lemma HdRel_ltk_value_unimportant :
    forall {k : X.t} {v1 v2 : D.t} {m : M.Raw.t D.t},
    HdRel M.Raw.PX.ltk (k, v1) m -> HdRel M.Raw.PX.ltk (k, v2) m.
  Proof. intros. destruct H; auto. Qed.

  Lemma adjusti_Sorted :
    forall (f : X.t -> D.t -> D.t) (k : X.t) (m : M.Raw.t D.t),
    Sorted M.Raw.PX.ltk m -> Sorted M.Raw.PX.ltk (raw_adjusti f k m).
  Proof.
    intros. induction H; simpl; auto. destruct a.
    cdestruct (X.compare k t0); constructor; try (apply adjusti_HdRel); auto.
    apply (HdRel_ltk_value_unimportant H0).
  Qed.

  Lemma adjust_Sorted :
    forall (f : D.t -> D.t) (k : X.t) (m : M.Raw.t D.t),
    Sorted M.Raw.PX.ltk m -> Sorted M.Raw.PX.ltk (raw_adjust f k m).
  Proof. intros. apply adjusti_Sorted. auto. Qed.

  Definition adjusti (f : X.t -> D.t -> D.t) (k : X.t) (m : M.t D.t) : M.t D.t :=
    M.Mk (adjusti_Sorted f k m.(M.this) m.(M.sorted)).

  Definition adjust (f : D.t -> D.t) (k : X.t) (m : M.t D.t) : M.t D.t :=
    M.Mk (adjust_Sorted f k m.(M.this) m.(M.sorted)).

  (* Proofs and stuff *)

  Instance eq_list_refl : Reflexive eq_list := {}.
  Proof.
    induction x.
    - reflexivity.
    - simpl. destruct a. rewrite M.Raw.MX.compare_refl. split.
      + reflexivity.
      + auto.
  Qed.
  Instance eq_list_sym : Symmetric eq_list := {}.
  Proof.
    induction x; induction y; simpl; try contradiction; auto.
    - destruct a. contradiction.
    - destruct a, a0. cdestruct (X.compare t0 t2); try contradiction.
      assert (Hsym := H). symmetry in Hsym.
      rewrite (iff_sym (M.Raw.MX.compare_eq_iff t2 t0)) in Hsym. rewrite Hsym.
      intro. destruct H0. split.
      + symmetry. auto.
      + auto.
  Qed.
  Instance eq_list_trans : Transitive eq_list := {}.
  Proof.
    induction x; induction y; induction z; simpl; try contradiction; auto.
    - destruct a0. contradiction.
    - destruct a, a0, a1.
      cdestruct (X.compare t0 t2); try contradiction.
      cdestruct (X.compare t2 t4); try contradiction.
      assert (tEqT3 : X.eq t0 t4). { rewrite H. auto. }
      rewrite (iff_sym (M.Raw.MX.compare_eq_iff t0 t4)) in tEqT3. rewrite tEqT3.
      intros. destruct H1, H2. split.
      + rewrite H1. auto.
      + apply IHx with (y := y); auto.
  Qed.
  Instance eq_list_equiv : Equivalence eq_list := {}.

  Instance Setoid : SC.Setoid (M.t D.t) := {
    equiv := eq
  }.

  Definition union_f (key : X.t) (oe1 oe2 : option D.t) : option D.t :=
    match oe1, oe2 with
    | None,    None    => None
    | None,    Some e2 => Some e2
    | Some e1, None    => Some e1
    | Some e1, Some e2 => Some (join e1 e2)
    end.

  Definition union : M.t D.t -> M.t D.t -> M.t D.t :=
    M.merge union_f.

  Instance JSL : JoinSemiLattice (M.t D.t) := {
    join := union
  }.

  Instance BJSL : BoundedJoinSemiLattice (M.t D.t) := {
    bottom := M.empty
  }.

  Lemma merge_l_union_id :
    forall (m : M.Raw.t D.t),
    M.Raw.merge_l union_f m = m.
  Proof.
    intros. induction m; simpl.
    - auto.
    - destruct a. rewrite IHm. auto.
  Qed.

  Lemma merge_r_union_id :
    forall (m : M.Raw.t D.t),
    M.Raw.merge_r union_f m = m.
  Proof.
    intros. induction m; simpl.
    - auto.
    - destruct a. rewrite IHm. auto.
  Qed.

  Lemma merge_union_nil_r :
    forall (m : M.Raw.t D.t),
    eq_list (M.Raw.merge union_f m nil) m.
  Proof.
    destruct m; simpl.
    - constructor.
    - destruct p. simpl. rewrite M.Raw.MX.compare_refl. split.
      + reflexivity.
      + rewrite merge_l_union_id. reflexivity.
  Qed.

  Lemma eq_to_compare : forall a b, X.eq a b -> X.compare a b = Eq.
  Proof. intros. rewrite (M.Raw.MX.compare_eq_iff a b). auto. Qed.

  Lemma lt_to_compare : forall a b, X.lt a b -> X.compare a b = Lt.
  Proof. intros. rewrite (M.Raw.MX.compare_lt_iff a b). auto. Qed.

  Lemma gt_to_compare : forall a b, X.lt a b -> X.compare b a = Gt.
  Proof. intros. rewrite (M.Raw.MX.compare_gt_iff b a). auto. Qed.

  Lemma merge_union_associative :
    forall (m1 m2 m3 : M.Raw.t D.t),
    eq_list (M.Raw.merge union_f m1 (M.Raw.merge union_f m2 m3))
            (M.Raw.merge union_f (M.Raw.merge union_f m1 m2) m3).
  Proof.
    Ltac crush :=
    repeat match goal with
    | |- context[M.Raw.merge_l union_f ?m] => rewrite (merge_l_union_id m); simpl
    | |- context[M.Raw.merge_r union_f ?m] => rewrite (merge_r_union_id m); simpl
    | |- context[M.Raw.merge union_f ?m nil] => rewrite (merge_union_nil_r m); simpl
    | Heq : X.eq ?a ?b |- context[X.compare ?a ?b] => rewrite (eq_to_compare a b Heq); simpl
    | Heq1 : X.eq ?a ?b, Heq2 : X.eq ?b ?c |- context[X.compare ?a ?c] =>
        rewrite (eq_to_compare a c (Equivalence_Transitive (A := X.t) a b c Heq1 Heq2)); simpl
    | Hlt : X.lt ?a ?b |- context[X.compare ?a ?b] =>
       rewrite (lt_to_compare a b Hlt); simpl
    | Hlt : X.lt ?a ?b |- context[X.compare ?b ?a] =>
       rewrite (gt_to_compare a b Hlt); simpl
    | Heq : X.eq ?a1 ?a2, Hlt : X.lt ?a2 ?b |- context[X.compare ?a1 ?b] =>
       rewrite <- Heq in Hlt; rewrite (lt_to_compare a1 b Hlt); simpl
    | Heq : X.eq ?a1 ?a2, Hlt : X.lt ?b ?a2 |- context[X.compare ?a1 ?b] =>
       rewrite <- Heq in Hlt; rewrite (gt_to_compare b a1 Hlt); simpl
    | |- context[X.compare ?t ?t] => rewrite M.Raw.MX.compare_refl
    | Heq : X.eq ?a1 ?a2, Hlt : X.lt ?b ?a1 |- context[X.compare ?b ?a2] =>
       rewrite Heq in Hlt; rewrite (lt_to_compare b a2 Hlt); simpl
    | Hlt1 : X.lt ?a1 ?a2, Hlt2 : X.lt ?a2 ?a3 |- context[X.compare ?a1 ?a3] =>
       rewrite (lt_to_compare a1 a3 (M.Raw.MX.lt_trans Hlt1 Hlt2)); simpl
    | Hlt1 : X.lt ?a1 ?a2, Hlt2 : X.lt ?a2 ?a3 |- context[X.compare ?a3 ?a1] =>
       rewrite (gt_to_compare a1 a3 (M.Raw.MX.lt_trans Hlt1 Hlt2)); simpl
    | |- context[match ?p with | pair _ _ => _ end] => destruct p; simpl
    | |- _ /\ _ => split
    | |- _ => auto; try reflexivity
    end.

    induction m1; induction m2; induction m3; simpl; crush.
    simpl in IHm2; simpl in IHm3;
    repeat rewrite merge_l_union_id in IHm2; repeat rewrite merge_l_union_id in IHm3;
    cdestruct (X.compare t0 t2); cdestruct (X.compare t2 t4); crush;
    simpl in IHm2; simpl in IHm3;
    repeat rewrite merge_l_union_id in IHm2; repeat rewrite merge_l_union_id in IHm3;
    auto.
    - pose proof (jslAssociativity (a := D.t)) as Assoc. specialize (Assoc t1 t3 t5).
      rewrite dequiv_is_deq in Assoc. auto.
    - specialize (IHm1 ((t2, t3) :: m2) ((t4, t5) :: m3)). simpl in IHm1.
      rewrite (eq_to_compare t2 t4 H0) in IHm1. auto.
    - specialize (IHm1 ((t2, t3) :: m2) ((t4, t5) :: m3)). simpl in IHm1.
      rewrite (lt_to_compare t2 t4 H0) in IHm1. auto.
    - simpl. cdestruct (X.compare t0 t4); simpl; crush.
      + specialize (IHm1 ((t2, t3) :: m2) m3). simpl in IHm1.
        repeat rewrite merge_l_union_id in IHm1. auto.
      + specialize (IHm1 ((t2, t3) :: m2) ((t4, t5) :: m3)). simpl in IHm1.
        repeat rewrite merge_l_union_id in IHm1.
        rewrite (gt_to_compare t4 t2 H0) in IHm1. auto.
    Qed.

  Lemma merge_union_commutative :
    forall (m1 m2 : M.Raw.t D.t),
    eq_list (M.Raw.merge union_f m1 m2) (M.Raw.merge union_f m2 m1).
  Proof.
    induction m1; simpl.
    - intros. rewrite merge_r_union_id. rewrite merge_union_nil_r. reflexivity.
    - induction m2; destruct a; simpl;
      repeat rewrite merge_l_union_id;
      repeat rewrite merge_r_union_id.
      + rewrite M.Raw.MX.compare_refl. split; reflexivity.
      + destruct a0. simpl. cdestruct (X.compare t0 t2).
        * assert (Hsym := H). symmetry in Hsym.
          rewrite (eq_to_compare t2 t0 Hsym). simpl.
          rewrite (eq_to_compare t0 t2 H). split.
          -- pose proof (jslCommutativity (a := D.t)) as Comm. specialize (Comm t1 t3).
             rewrite dequiv_is_deq in Comm. auto.
          -- auto.
        * rewrite (gt_to_compare t0 t2 H). simpl.
          rewrite M.Raw.MX.compare_refl. split.
          -- reflexivity.
          -- specialize (IHm1 ((t2, t3) :: m2)). simpl in IHm1.
             repeat rewrite merge_l_union_id in IHm1. auto.
        * rewrite (lt_to_compare t2 t0 H). simpl.
          rewrite M.Raw.MX.compare_refl. split.
          -- reflexivity.
          -- repeat rewrite merge_l_union_id in IHm2. auto.
  Qed.

  Lemma merge_union_idempotent :
    forall (m : M.Raw.t D.t),
    eq_list (M.Raw.merge union_f m m) m.
  Proof.
    induction m; simpl.
    + constructor.
    + destruct a. rewrite M.Raw.MX.compare_refl. simpl.
      rewrite M.Raw.MX.compare_refl. split.
      * pose proof (jslIdempotency (a := D.t)) as Idem. specialize (Idem t1).
        rewrite dequiv_is_deq in Idem. auto.
      * auto.
  Qed.

  Instance VJSL : VJoinSemiLattice (M.t D.t) := {}.
  Proof.
  - destruct x, y, z. apply merge_union_associative.
  - destruct x, y. apply merge_union_commutative.
  - destruct x. apply merge_union_idempotent.
  Qed.

  Instance VBJSL :
    forall `{VJoinSemiLattice D.t},
    VBoundedJoinSemiLattice (M.t D.t) := {}.
  Proof. destruct x. apply merge_union_nil_r. Qed.

  Instance show_t : Show (M.t D.t) := {
    show m := "of_list " ++ show (M.bindings m)
  }.
End VMMap.