
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

Require Import Coq.Lists.List.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.ArchMM.
Require Import Hafnium.Concrete.Assumptions.Constants.
Require Import Hafnium.Concrete.Assumptions.Datatypes.
Require Import Hafnium.Concrete.MM.Datatypes.

(*** This file defines the starting parameters for the concrete state. It is kept
   separate so that definitions using concrete_params can be used in State.v ***)

Record vm :=
  {
    vm_ptable : mm_ptable;
    vm_id : nat;
  }.

(* N.B. there can be multiple page tables at the root level *)
Definition vm_root_tables (v : vm) : list ptable_pointer :=
  ptr_from_va (va_from_pa v.(vm_ptable).(root)).

(* starting parameters -- don't change *)
Class concrete_params :=
  {
    vms : list vm;
    hafnium_ptable : mm_ptable;
  }.

(* N.B. there can be multiple page tables at the root level *)
Definition hafnium_root_tables {cp : concrete_params} : list ptable_pointer :=
  ptr_from_va (va_from_pa hafnium_ptable.(root)).

Definition all_root_ptables {cp : concrete_params} : list mm_ptable :=
  hafnium_ptable :: map vm_ptable vms.

Definition all_root_ptable_pointers {cp : concrete_params}
  : list ptable_pointer := hafnium_root_tables ++ flat_map vm_root_tables vms.

Class params_valid {cp : concrete_params} :=
  {
    correct_number_of_root_tables_stage1 :
      length (ptr_from_va (va_from_pa (hafnium_ptable.(root))))
      = arch_mm_stage1_root_table_count;
    correct_number_of_root_tables_stage2 :
      forall t,
        In t (map vm_ptable vms) ->
        length (ptr_from_va (va_from_pa t.(root)))
        = arch_mm_stage2_root_table_count;
    no_duplicate_ptables : NoDup all_root_ptables;
    no_duplicate_ids : NoDup (map vm_id vms)
  }.
