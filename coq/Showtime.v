From Showtime Require Import Error Max MSet State.
Require Import Arith.Wf_nat Bool List Omega.
Require Import Structures.OrdersEx.
Open Scope string_scope.

Module Snat  := MSets.MSetAVL.Make Nat_as_OT.
Module VSnat := VMSet Nat_as_OT Snat.

Definition SetTID := Snat.t.

Definition tickN (delta : Time) (myi : TID) (s : State) : State :=
  match s with
  | MkState tl l1 => MkState (VM.adjust (fun x => x + delta) myi tl) l1
  end.

Definition tick : TID -> State -> State :=
  tickN (nat_to_Max 1).

Definition epsilon : Time :=
  nat_to_Max 1.

Definition myEpsilon (n : TID) : Time :=
  nat_to_Max (n + 1) * epsilon.

Definition unstableLogPrefix (t : Time) (lg : Log) : list (Time * TID) :=
  VS.SProps.to_list (S.filter (fun x => fst x <=? t) lg).

Definition readParticipants (t : Time) (s : State) : option SetTID :=
  match s with
  | MkState tv lg =>
      if VM.MProps.exists_range (fun x => x <? t) tv
         then None
         else Some (VSnat.SProps.of_list (map snd (unstableLogPrefix t lg)))
  end.

Definition myTime (myi : TID) (s : State) : Time :=
  match s with
  | MkState tv _ =>
    match M.MapS.find myi tv with
    | Some t => t
    | None => patternFailure (* Partiality! *)
    end
  end.

Definition showLen : Time := nat_to_Max 10.

Definition dropWhile {a} (p : a -> bool) : list a -> list a :=
  fix go (xs : list a) : list a :=
    match xs with
    | nil => nil
    | x :: xs' =>
        if p x
           then go xs'
           else xs
    end.

Lemma induction_ltof1_Prop
     : forall (A : Set) (f : A -> nat) (P : A -> Prop),
       (forall x : A, (forall y : A, ltof A f y x -> P y) -> P x) ->
       forall a : A, P a.
Proof.
  intros A f P F.
  assert (H : forall (n : nat) (a : A), (f a < n)%nat -> P a).
  { induction n; intros.
    - omega.
    - apply F. unfold ltof. intros. apply IHn.
      apply Nat.lt_le_trans with (m := f a); omega. }
  intros. apply H with (n := S (f a)). omega.
Defined.

Definition flip_ltb (x : Max) : Max -> bool :=
  fun (y : Max) => y <? x.

Inductive
  OpenAcc : list Time -> Prop :=
  | OpenAccNil  : OpenAcc nil
  | OpenAccCons : forall t0 rst,
                  ClosedAcc (t0 + showLen) rst ->
                  OpenAcc (t0 :: rst)
with
  ClosedAcc : Time -> list Time -> Prop :=
  | ClosedAccNil  : forall expiry, ClosedAcc expiry nil
  | ClosedAccCons : forall expiry t1 rst,
                    ClosedAcc (expiry + showLen) (dropWhile (flip_ltb expiry) rst) ->
                    OpenAcc (t1 :: rst) ->
                    ClosedAcc expiry (t1 :: rst).

Lemma OpenAcc_inv :
  forall {l : list Time} {t0 : Time} {rst : list Time},
  OpenAcc l -> l = (t0 :: rst) ->
  ClosedAcc (t0 + showLen) rst.
Proof. intros. subst. inversion H. auto. Defined.

Lemma ClosedAcc_inv_1 :
  forall {expiry : Time} {ls : list Time} {t1 : Time} {rst : list Time},
  ClosedAcc expiry ls -> ls = (t1 :: rst) ->
  ClosedAcc (expiry + showLen) (dropWhile (flip_ltb expiry) rst).
Proof. intros. subst. inversion H. auto. Defined.

Lemma ClosedAcc_inv_2 :
  forall {expiry : Time} {ls : list Time} {t1 : Time} {rst : list Time},
  ClosedAcc expiry ls -> ls = (t1 :: rst) ->
  OpenAcc (t1 :: rst).
Proof. intros. subst. inversion H. auto. Defined.

Fixpoint
  open' (ls : list Time) (acc : OpenAcc ls) {struct acc} : list Time :=
    match ls as ls0 return (ls = ls0 -> list Time) with
    | nil =>
        fun (_ : ls = nil) => nil
    | t0 :: rst =>
        fun (H : ls = (t0 :: rst)) =>
        t0 :: closed' (t0 + showLen) rst (OpenAcc_inv acc H)
    end (eq_refl ls)
with
  closed' (expiry : Time) (ls : list Time)
          (acc : ClosedAcc expiry ls) {struct acc} : list Time :=
    match ls as ls0 return (ls = ls0 -> list Time) with
    | nil =>
        fun (_ : ls = nil) => nil
    | t1 :: rst =>
        fun (H : ls = (t1 :: rst)) =>
        if t1 <? expiry
        then expiry :: closed' (expiry + showLen)
                               (dropWhile (flip_ltb expiry) rst)
                               (ClosedAcc_inv_1 acc H)
        else open' (t1 :: rst) (ClosedAcc_inv_2 acc H)
    end (eq_refl ls).

Lemma dropWhile_length :
  forall {a} (f : a -> bool) (l : list a),
  (length (dropWhile f l) <= length l)%nat.
Proof.
  induction l; simpl; auto.
  destruct (f a0); simpl; auto.
Defined.

Theorem
  openAcc : forall (ls : list Time), OpenAcc ls
with
  closedAcc : forall (expiry : Time) (ls : list Time), ClosedAcc expiry ls.
Proof.
- induction ls; constructor. apply closedAcc.
- intros. change (ClosedAcc expiry ls) with (prod_curry ClosedAcc (expiry, ls)).
  apply (induction_ltof1_Prop (Time * list Time)
                              (prod_curry (fun _ => @length Time))
                              (prod_curry ClosedAcc)).
  intros. destruct x. destruct l as [|x xs]; constructor.
  + change (ClosedAcc (t + showLen) (dropWhile (flip_ltb t) xs))
      with (prod_curry ClosedAcc (t + showLen, (dropWhile (flip_ltb t) xs))).
    apply H. unfold ltof, prod_curry.
    pose proof (dropWhile_length (flip_ltb t) xs). simpl.
    apply le_lt_n_Sm. auto.
  + constructor.
    change (ClosedAcc (x + showLen) xs)
      with (prod_curry ClosedAcc (x + showLen, xs)).
    apply H. unfold ltof, prod_curry. simpl. omega.
Defined.
Scheme OpenAcc_ind_dep   := Induction for OpenAcc   Sort Prop.
Scheme ClosedAcc_ind_dep := Induction for ClosedAcc Sort Prop.
Scheme OpenAcc_ind_dep_mut   := Induction for OpenAcc   Sort Prop
  with ClosedAcc_ind_dep_mut := Induction for ClosedAcc Sort Prop.

Definition open (ls : list Time) : list Time :=
  open' ls (openAcc ls).
Definition closed (expiry : Time) (ls : list Time) : list Time :=
  closed' expiry ls (closedAcc expiry ls).
Definition showtimes : list Time -> list Time := open.

Lemma open'_PI' :
  forall {l1} (acc1 : OpenAcc l1) {l2} (acc2 : OpenAcc l2),
  l1 = l2 ->
  open' l1 acc1 = open' l2 acc2.
Proof.
  apply (OpenAcc_ind_dep_mut
        (fun (l' : list Time) (acc' : OpenAcc l') =>
         forall (l2 : list Time) (acc2 : OpenAcc l2),
         l' = l2 -> open' l' acc' = open' l2 acc2)
        (fun (expiry' : Time) (l' : list Time) (acc' : ClosedAcc expiry' l') =>
         forall (expiry2 : Time) (l2 : list Time) (acc2 : ClosedAcc expiry2 l2),
         expiry' = expiry2 -> l' = l2 ->
         closed' expiry' l' acc' = closed' expiry2 l2 acc2)).
  - apply (OpenAcc_ind_dep_mut
          (fun (l' : list Time) (acc' : OpenAcc l') =>
           nil = l' -> open' nil OpenAccNil = open' l' acc')
          (fun _ _ _ => True)); try discriminate; auto.
  - intros t0 rst c ClosedH.
    apply (OpenAcc_ind_dep_mut
          (fun (l' : list Time) (acc' : OpenAcc l') =>
           t0 :: rst = l' -> open' (t0 :: rst) (OpenAccCons t0 rst c) = open' l' acc')
          (fun _ _ _ => True)); try discriminate; auto. simpl. intros.
    injection H0 as X Y. subst. f_equal. apply ClosedH; auto.
  - intro expiry.
    apply (ClosedAcc_ind_dep_mut
           (fun _ _ => True)
           (fun (expiry' : Time) (l' : list Time) (acc' : ClosedAcc expiry' l') =>
            expiry = expiry' -> nil = l' ->
            closed' expiry nil (ClosedAccNil expiry) = closed' expiry' l' acc'));
    try discriminate; auto.
  - intros expiry t1 rst c ClosedH o OpenH.
    apply (ClosedAcc_ind_dep_mut
           (fun _ _ => True)
           (fun (expiry' : Time) (l' : list Time) (acc' : ClosedAcc expiry' l') =>
            expiry = expiry' -> t1 :: rst = l' ->
            closed' expiry (t1 :: rst) (ClosedAccCons expiry t1 rst c o)
              = closed' expiry' l' acc')); try discriminate; auto. intros. simpl.
    injection H2 as X Y. subst. bdestruct (t0 <? expiry0).
    + f_equal. apply ClosedH; auto.
    + apply OpenH; auto.
Qed.

Lemma closed'_PI' :
  forall {expiry1 l1} (acc1 : ClosedAcc expiry1 l1)
         {expiry2 l2} (acc2 : ClosedAcc expiry2 l2),
  expiry1 = expiry2 -> l1 = l2 ->
  closed' expiry1 l1 acc1 = closed' expiry2 l2 acc2.
Proof.
  apply (ClosedAcc_ind_dep
        (fun (expiry' : Time) (l' : list Time) (acc' : ClosedAcc expiry' l') =>
         forall (expiry2 : Time) (l2 : list Time) (acc2 : ClosedAcc expiry2 l2),
         expiry' = expiry2 -> l' = l2 ->
         closed' expiry' l' acc' = closed' expiry2 l2 acc2)).
  - intro expiry.
    apply (ClosedAcc_ind_dep
          (fun (expiry' : Time) (l' : list Time) (acc' : ClosedAcc expiry' l') =>
           expiry = expiry' -> nil = l' ->
           closed' expiry nil (ClosedAccNil expiry) = closed' expiry' l' acc'));
    try discriminate. reflexivity.
  - intros expiry t1 rst c H o.
    apply (ClosedAcc_ind_dep
          (fun (expiry' : Time) (l' : list Time) (acc' : ClosedAcc expiry' l') =>
           expiry = expiry' -> t1 :: rst = l' ->
           closed' expiry (t1 :: rst) (ClosedAccCons expiry t1 rst c o) =
           closed' expiry' l' acc')); try discriminate. intros.
    injection H2 as H3 H4. subst. simpl. bdestruct (t0 <? expiry0).
    + f_equal. apply H; auto.
    + apply open'_PI'. auto.
Qed.

Lemma open'_PI :
  forall {l} (acc1 acc2 : OpenAcc l),
  open' l acc1 = open' l acc2.
Proof. intros. apply open'_PI'. auto. Qed.

Lemma closed'_PI :
  forall {expiry l} (acc1 acc2 : ClosedAcc expiry l),
  closed' expiry l acc1 = closed' expiry l acc2.
Proof. intros. apply closed'_PI'; auto. Qed.

Theorem open'_nil :
  forall (acc : OpenAcc nil),
  open' nil acc = nil.
Proof. intros. rewrite (open'_PI' acc OpenAccNil); auto. Qed.

Theorem open_nil : open nil = nil.
Proof. auto. Qed.

Theorem open'_cons :
  forall {t0 rst} acc1 acc2,
  open' (t0 :: rst) acc1 = t0 :: closed' (t0 + showLen) rst acc2.
Proof. intros. rewrite (open'_PI' acc1 (OpenAccCons t0 rst acc2)); auto. Qed.

Theorem open'_cons_alt :
  forall {t0 rst} acc,
  open' (t0 :: rst) (OpenAccCons t0 rst acc) = t0 :: closed' (t0 + showLen) rst acc.
Proof. intros. apply open'_cons. Qed.

Theorem open_cons :
  forall {t0 rst},
  open (t0 :: rst) = t0 :: closed (t0 + showLen) rst.
Proof. intros. apply open'_cons. Qed.

Theorem closed'_nil :
  forall {expiry} (acc : ClosedAcc expiry nil),
  closed' expiry nil acc = nil.
Proof. intros. rewrite (closed'_PI' acc (ClosedAccNil expiry)); auto. Qed.

Theorem closed_nil :
  forall {expiry},
  closed expiry nil = nil.
Proof. auto. Qed.

Theorem closed'_cons :
  forall {expiry t1 rst} acc1 acc2 acc3,
  closed' expiry (t1 :: rst) acc1 =
    if t1 <? expiry
    then expiry :: closed' (expiry + showLen)
                           (dropWhile (flip_ltb expiry) rst)
                           acc2
    else open' (t1 :: rst) acc3.
Proof. intros. rewrite (closed'_PI' acc1 (ClosedAccCons _ _ _ acc2 acc3)); auto. Qed.

Theorem closed'_cons_alt :
  forall {expiry t1 rst} acc1 acc2,
  closed' expiry (t1 :: rst) (ClosedAccCons expiry t1 rst acc1 acc2) =
    if t1 <? expiry
    then expiry :: closed' (expiry + showLen)
                           (dropWhile (flip_ltb expiry) rst)
                           acc1
    else open' (t1 :: rst) acc2.
Proof. intros. apply closed'_cons. Qed.

Theorem closed_cons :
  forall {expiry t1 rst},
  closed expiry (t1 :: rst) =
    if t1 <? expiry
    then expiry :: closed (expiry + showLen)
                          (dropWhile (flip_ltb expiry) rst)
    else open (t1 :: rst).
Proof. intros. apply closed'_cons. Qed.