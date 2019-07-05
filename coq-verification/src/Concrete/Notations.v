Require Import Coq.NArith.BinNat.
Require Import Hafnium.Concrete.Datatypes.

(*** This file is mostly boilerplate to coerce Coq's notation system into making
     the model more readable ***)

(* nicer display of mm_mode operations *)
Notation "x &~ y" := (N.land x (N.lnot y (N.size x))) (at level 199) : N_scope.
Infix "|||" := N.lor (at level 199) : N_scope.
Infix "&" := N.land (at level 199) : N_scope.
Infix ">>" := N.shiftr (at level 199) : N_scope.
Infix "<<" := N.shiftl (at level 199) : N_scope.

Bind Scope N_scope with mode_t.
Bind Scope N_scope with attributes.
Bind Scope N_scope with uintpaddr_t.
Bind Scope N_scope with uintvaddr_t.

Notation "! x" := (negb x) (at level 200) : bool_scope.
Notation "x != y" := (negb (N.eqb x y)) (at level 199) : bool_scope.

Coercion N.of_nat : nat >-> N. (* change nat to N automatically *)
Set Printing Coercions. (* when printing, show N.of_nat explicitly *)
