Require Import Arith Bool.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

Ltac cdestruct X :=
  let H := fresh in let e1 := fresh "e1" in let e2 := fresh "e2" in let e3 := fresh "e3" in
   evar (e1: Prop); evar (e2: Prop); evar (e3: Prop);
   assert (H: CompareSpec e1 e2 e3 X); subst e1; subst e2; subst e3;
    [eauto with cdestruct
    | destruct H as [H|H|H] ].