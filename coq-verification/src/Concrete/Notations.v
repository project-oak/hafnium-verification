Require Import Coq.NArith.BinNat.
Require Import Hafnium.Concrete.Datatypes.

(*** This file is mostly boilerplate to coerce Coq's notation system into making
     the model more readable ***)

(* nicer display of mm_mode operations *)
Definition mm_mode_set_flag (m : int) (flag : nat) : int :=
  N.setbit m (N.of_nat flag).
Definition mm_mode_get_flag (m : int) (flag : nat) : bool :=
  N.testbit m (N.of_nat flag).
Notation "[ x | .. | y ]" :=
  (mm_mode_set_flag .. (mm_mode_set_flag 0 x) .. y)
    (at level 49, y at level 0, only parsing) : N_scope.
Notation "x & y " :=
  (mm_mode_get_flag x y)
    (at level 49, y at level 0, only parsing) : N_scope.

Bind Scope N_scope with mode_t.
Bind Scope N_scope with attributes.
Bind Scope N_scope with uintpaddr_t.
Bind Scope N_scope with uintvaddr_t.

Notation "! x" := (negb x) (at level 200) : bool_scope.

Coercion N.of_nat : nat >-> N. (* change nat to N automatically *)
Set Printing Coercions. (* when printing, show N.of_nat explicitly *)
