(*
 * Copyright 2019 Jade Philipoom
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

Require Import Coq.NArith.BinNat.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Util.List.

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
Notation "x != y" := (negb (N.eqb x y)) (at level 199) : N_scope.

Coercion N.of_nat : nat >-> N. (* change nat to N automatically *)
Set Printing Coercions. (* when printing, show N.of_nat explicitly *)

Notation "x [[ y ]]" :=
  (nth_default_oobe x y) (at level 199, only parsing).
