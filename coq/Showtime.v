From Showtime Require Import Destruct Error ListAsOT Max MSet Op OpInst State.
Require Import Arith.Wf_nat Bool List Omega.
Require Import Structures.Orders Structures.OrdersEx.
Open Scope string_scope.

Module SetNat  := MSets.MSetAVL.Make Nat_as_OT.
Module VSetNat := VMSet Nat_as_OT SetNat.

Definition SetTID := SetNat.t.

Definition tickN (delta : Time) (myi : TID) (s : State) : State :=
  match s with
  | MkState tl l1 => MkState (VMapNat2Max.adjust (fun x => x + delta) myi tl) l1
  end.

Definition tick : TID -> State -> State :=
  tickN (nat_to_Max 1).

Definition epsilon : Time :=
  nat_to_Max 1.

Definition myEpsilon (n : TID) : Time :=
  nat_to_Max (n + 1) * epsilon.

Definition unstableLogPrefix (t : Time) (lg : Log) : list (Time * TID) :=
  VSetPairMaxNat.SProps.to_list (SetPairMaxNat.filter (fun x => fst x <=? t) lg).

Definition readParticipants (t : Time) (s : State) : option SetTID :=
  match s with
  | MkState tv lg =>
      if VMapNat2Max.MProps.exists_range (fun x => x <? t) tv
         then None
         else Some (VSetNat.SProps.of_list (map snd (unstableLogPrefix t lg)))
  end.

Definition myTime (myi : TID) (s : State) : Time :=
  match s with
  | MkState tv _ =>
    match MapNat2Max.find myi tv with
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

Definition flip_geb (x : Max) : Max -> bool :=
  fun (y : Max) => y >=? x.

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

Definition option_bind {a b} (oa : option a) (k : a -> option b) : option b :=
  match oa with
  | Some x => k x
  | None   => None
  end.

Notation "o >>= k" := (option_bind o k) (at level 10, left associativity).

Fixpoint ourShow (myi : TID) (s0 : State) : list Time -> option Time :=
  fix go (l : list Time) : option Time :=
    match l with
    | nil => None
    | t :: rst =>
      readParticipants t s0 >>=
      fun set =>
        if SetNat.mem myi set
        then Some t
        else go rst
    end.

Definition minimum (l : list Time) : Time :=
  fold_left Max.min l (hd default l). (* Partiality! *)

Definition pref (tv : TimeMap) (lg : Log) : list (Time * TID) :=
  unstableLogPrefix (minimum (map snd (MapNat2Max.bindings tv))) lg.

Definition times (tv : TimeMap) (lg : Log) : list Time :=
  showtimes (map fst (pref tv lg)).

Definition myt : TID -> State -> Time :=
  myTime.

Definition result (myi : TID) (s0 : State) : option Time :=
  match s0 with
  | MkState tv lg =>
      ourShow myi s0 (dropWhile (flip_ltb (myt myi s0 - showLen)) (times tv lg))
  end.

Definition getNextShow : TID -> State -> option Time := result.

Definition openTimeDelta : Time := nat_to_Max 1.

Definition openResource (me : TID) (s0 : State) : option (State * Time) :=
  match s0 with
  | MkState tv lg =>
      let myt0 := myTime me s0 in
      let lg2  := SetPairMaxNat.add (myt0, me) lg in
      let s1   := tickN openTimeDelta me (MkState tv lg2) in
        getNextShow me s1 >>=
      fun t1 =>
        let myJoinTime := t1 + myEpsilon me in
        if t1 >? myt0
        then Some (tickN (myJoinTime - myt0) me s1, t1)
        else Some (s1, t1)
  end.

Definition Prog := list (list Op).

Definition Oplog := list OpInst.

Definition LabeledProg := list (TID * list Op).

Definition Conf := (State * LabeledProg * Oplog)%type.

Definition oths (set : SetTID) (st : State) : list Time :=
  map (fun i => myTime i st) (SetNat.elements set).

Definition amLMIC (myi : TID) (set : SetTID) (st : State) : bool :=
  forallb (flip_geb (myt myi st)) (oths set st).

Definition defaultFuel : nat := 15.

Definition numThreads : Prog -> nat :=
  @length (list Op).

Definition null {a} (l : list a) : bool :=
  match l with
  | nil    => true
  | _ :: _ => false
  end.

Definition isProgDone (_s : State) : LabeledProg -> bool :=
  forallb (fun x => null (snd x)).

Definition mapOption {a b} (f : a -> option b) : list a -> list b :=
  fix go (l : list a) : list b :=
    match l with
    | nil => nil
    | x :: xs =>
        let rs := go xs in
        match f x with
        | None   => rs
        | Some r => r :: rs
        end
    end.

Definition catSomes {a} : list (option a) -> list a :=
  mapOption id.

Definition startState (ops: Prog) : State :=
  MkState (VMapNat2Max.MProps.of_list (map (fun i => (i, myEpsilon i))
                                      (seq 0 (numThreads ops))))
          SetPairMaxNat.empty.

Module ListOp_as_OT :=
  list_as_OT Op_as_OT.
Module Prog_as_OT :=
  list_as_OT ListOp_as_OT.
Module LabeledProgElem_as_OT :=
  PairOrderedType Nat_as_OT ListOp_as_OT.
Module LabeledProg_as_OT :=
  list_as_OT LabeledProgElem_as_OT.
Module Oplog_as_OT :=
  list_as_OT OpInst_as_OT.
Module SetOplog :=
  MSets.MSetAVL.Make Oplog_as_OT.
Module VSetOplog :=
  VMSet Oplog_as_OT SetOplog.

Module TripleOrderedType (A : OrderedType)
                          (B : OrderedType)
                          (C : OrderedType) <: OrderedType.
  Module AB := PairOrderedType A B.
  Module ABC := PairOrderedType AB C.
  Include ABC.
End TripleOrderedType.

Module Conf_as_OT :=
  TripleOrderedType State_as_OT LabeledProg_as_OT Oplog_as_OT.
Module SetConf  := MSets.MSetAVL.Make Conf_as_OT.
Module VSetConf := VMSet Conf_as_OT SetConf.

Definition splitAt {a} (n : nat) (xs : list a) : (list a * list a) :=
  (firstn n xs, skipn n xs).

(* TODO: This is actually 100000 in the prototype, but using that causes
   Coq to overflow its stack *)
Definition inf : Time := nat_to_Max 1000.

Definition expandHelper (s0 : State) (ps0 : LabeledProg) (ol : Oplog) (thrd : nat) : option Conf :=
  match splitAt thrd ps0 with
  | (frnt, (myid, nil) :: bk) =>
      Some (tickN inf myid s0, frnt ++ bk, ol)
  | (frnt, (myid, op :: rst) :: bk) =>
      let remaining := (frnt ++ (myid, rst) :: bk) in
      match op with
      | Open =>
          match openResource myid s0 with
          | None => None
          | Some (s1, showStrt) =>
              Some (s1, frnt ++ (myid, BlockedOpen showStrt :: rst) :: bk, ol)
          end
      | BlockedOpen showStrt =>
          match readParticipants showStrt s0 with
          | None => None
          | Some locals =>
              if amLMIC myid locals s0
              then Some (s0, remaining, ol ++ (MkOpInst myid (myTime myid s0) Open :: nil))
              else None
          end
      | Compute dt => Some (tickN dt myid s0, remaining, ol)
      end
  | (_frnt, nil) => patternFailure (* Partiality! *)
  end.

Definition expand (c : Conf) : SetConf.t :=
  match c with
  | (s0, ps0, ol) =>
      VSetConf.SProps.of_list (catSomes (map (expandHelper s0 ps0 ol)
                                             (seq 0 (length ps0))))
  end.

Fixpoint explore (fuel : nat) (visited next : SetConf.t) : (SetConf.t * SetConf.t) :=
  match fuel with
  | O => (visited, next)
  | S fuel' =>
    if SetConf.is_empty next
    then (visited, next)
    else let next'    := fold_left SetConf.union
                                   (map expand (SetConf.elements next))
                                   SetConf.empty in
         let visited' := SetConf.union visited next in
         let whatsnew := SetConf.diff next' visited' in
         explore fuel' visited' whatsnew
  end.

Definition done : SetConf.t -> SetConf.t :=
  SetConf.filter (fun c => match c with | (s, p, _) => isProgDone s p end).

Module StateOplog_as_OT :=
  PairOrderedType State_as_OT Oplog_as_OT.
Module StateProgOplog_as_OT :=
  TripleOrderedType State_as_OT Prog_as_OT Oplog_as_OT.
Module SetStateOplog :=
  MSets.MSetAVL.Make StateOplog_as_OT.
Module VSetStateOplog :=
  VMSet StateOplog_as_OT SetStateOplog.
Module SetStateProgOplog :=
  MSets.MSetAVL.Make StateProgOplog_as_OT.
Module VSetStateProgOplog :=
  VMSet StateProgOplog_as_OT SetStateProgOplog.

Module MapNat2ListOp' := MMaps.MMapList.Make_ord Nat_as_OT ListOp_as_OT.
Module MapNat2ListOp  := MapNat2ListOp'.MapS.
Module VMapNat2ListOp := MMaps.MMapFacts.WProperties_fun Nat_as_OT MapNat2ListOp.

Definition fromOption {a} (def : a) (oa : option a) : a :=
  match oa with
  | None   => def
  | Some a => a
  end.

Definition dense (n : nat) (prs : LabeledProg) : Prog :=
  let mp := VMapNat2ListOp.of_list prs in
  map (fun i => fromOption nil (MapNat2ListOp.find i mp)) (seq 0 n).

Definition interp2 (ops : Prog) : (SetStateOplog.t * SetStateProgOplog.t) :=
  let zipped_ops := combine (seq 0 (length ops)) ops in
  let (final, unreached) :=
        explore defaultFuel SetConf.empty
                (SetConf.singleton (startState ops, zipped_ops, nil)) in
  let s1 := VSetStateOplog.SProps.of_list
            (map (fun c => match c with | (a, _, b) => (a, b) end)
                 (SetConf.elements (done final))) in
  let s2 := VSetStateProgOplog.SProps.of_list
            (map (fun c => match c with | (s, p, ol) => (s, dense (numThreads ops) p, ol) end)
                 (SetConf.elements unreached)) in
  (s1, s2).

Definition summarize (ss : (SetStateOplog.t * SetStateProgOplog.t)) : (option Oplog * nat) :=
  let (s1, s2) := ss in
  let logs := VSetOplog.SProps.of_list (map snd (SetStateOplog.elements s1)) in
  (* TODO: This call to elements seems redundant. *)
  match SetOplog.elements logs with
  | ans :: nil => (Some ans, SetStateProgOplog.cardinal s2)
  | nil        => (None,     SetStateProgOplog.cardinal s2)
  | ls         => error ("Impossible! Nondeterministic outcome!") (* Partiality *)
  end.

Definition threadOrder (p : Prog) : list nat :=
  match summarize (interp2 p) with
  | (None,    n) => error "Not enough fuel to reduce, leftover states" (* Partiality! *)
  | (Some ol, _) => map (fun oi => match oi with | MkOpInst i _ _ => i end) ol
  end.