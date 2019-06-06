From QuickChick Require Import Show.
From Showtime Require Import ListAsOT.
Require Import Structures.Equalities Structures.Orders Structures.OrdersEx.

Module Type IsShow (Import T : Typ).
  Declare Instance show_t : Show t.
End IsShow.

Module Type OrderedShowType := OrderedType <+ IsShow.

Module Nat_as_OST <: OrderedShowType.
  Include Nat_as_OT.
  Instance show_t : Show nat := showNat.
End Nat_as_OST.

Module PairOrderedShowType (A : OrderedShowType)
                            (B : OrderedShowType) <: OrderedShowType.
  Module AB_as_OT := PairOrderedType A B.
  Include AB_as_OT.
  Instance show_t : Show AB_as_OT.t := showPair.
End PairOrderedShowType.

Module TripleOrderedShowType (A : OrderedShowType)
                              (B : OrderedShowType)
                              (C : OrderedShowType) <: OrderedShowType.
  Module AB := PairOrderedShowType A B.
  Include PairOrderedShowType AB C.
End TripleOrderedShowType.

Module list_as_OST (O : OrderedShowType) <: OrderedShowType.
  Module List := list_as_OT O.
  Include List.
  Instance show_t : Show List.t := showList.
End list_as_OST.