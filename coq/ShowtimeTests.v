From Showtime Require Import Max Op Showtime State.
Require Import Lists.List.
Import Lists.List.ListNotations.

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