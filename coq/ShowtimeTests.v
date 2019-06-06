From QuickChick Require Import Show.
From Showtime Require Import Max Op Showtime State.
Require Import Lists.List.
Import Lists.List.ListNotations.
Open Scope string_scope.

Definition seven    : Time := nat_to_Max 7.
Definition eight    : Time := nat_to_Max 8.
Definition nine     : Time := nat_to_Max 9.
Definition ten      : Time := nat_to_Max 10.
Definition eleven   : Time := nat_to_Max 11.
Definition thirteen : Time := nat_to_Max 13.
Definition hundred  : Time := nat_to_Max 100.

Definition t0   : Prog := [[Open]].
Definition t1   : Prog := [[Open];[Open]].
Definition t2   : Prog := [[Compute ten;Open];[Open]].
Definition t3   : Prog := [[Compute ten;Open];[Compute ten;Open]].
Definition t4   : Prog := [[Compute ten;Open];[Compute nine;Open]].
Definition t5   : Prog := [[Open];[Open];[Open]].
Definition t6   : Prog := [[Compute ten;Open];[Compute seven;Compute seven;Open];[Open;Compute hundred]].
Definition t7   : Prog := [[Open];[Compute eight;Open]].
Definition t8   : Prog := [[Open];[Compute eleven;Open]].
Definition t9   : Prog := [[Open;Compute nine;Open];[Compute thirteen;Open]].
Definition t10  : Prog := [[Open;Compute nine;Open];[Compute eight;Open]].
Definition t10b : Prog := [[Open;Compute eleven;Open];[Compute seven;Open]].
Definition t11  : Prog := [[Open;Compute nine;Open];[Compute eight;Open];[Compute eight;Open]].
Definition t12  : Prog := [[Open;Open];[Open]].

Theorem ut0   : threadOrder t0   = [0].       Proof. auto. Qed.
Theorem ut1   : threadOrder t1   = [0;1].     Proof. auto. Qed.
Theorem ut2   : threadOrder t2   = [1;0].     Proof. auto. Qed.
Theorem ut3   : threadOrder t3   = [0;1].     Proof. auto. Qed.
Theorem ut4   : threadOrder t4   = [1;0].     Proof. auto. Qed.
Theorem ut5   : threadOrder t5   = [0;1;2].   Proof. auto. Qed.
Theorem ut6   : threadOrder t6   = [2;0;1].   Proof. auto. Qed.
Theorem ut7   : threadOrder t7   = [0;1].     Proof. auto. Qed.
Theorem ut8   : threadOrder t8   = [0;1].     Proof. auto. Qed.
Theorem ut9   : threadOrder t9   = [0;0;1].   Proof. auto. Qed.
Theorem ut10  : threadOrder t10  = [0;0;1].   Proof. auto. Qed.
Theorem ut10b : threadOrder t10b = [0;1;0].   Proof. auto. Qed.
Theorem ut11  : threadOrder t11  = [0;0;1;2]. Proof. auto. Qed.
Theorem ut12  : threadOrder t12  = [0;0;1].   Proof. auto. Qed.

Theorem ut_two_empty_programs   : threadOrder [[];[]]    = []. Proof. auto. Qed.
Theorem ut_three_empty_programs : threadOrder [[];[];[]] = []. Proof. auto. Qed.