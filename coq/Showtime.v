From Showtime Require Import Error Max MSet State.
Require Import List String.
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

(*
TODO: How to convince Coq that this terminates?

Fixpoint open (ls : list Time) {struct ls} : list Time :=
  match ls with
  | nil       => nil
  | t0 :: rst => t0 :: closed (t0 + showLen) rst
  end

  with
    closed (expiry : Time) (ls : list Time) {struct ls} : list Time :=
      match ls with
      | nil       => nil
      | t1 :: rst =>
        if t1 <? expiry
           then expiry :: closed (expiry + showLen) (dropWhile (fun x => x <? expiry) rst)
           else open (t1 :: rst)
      end.
*)