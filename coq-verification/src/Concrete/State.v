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
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Hafnium.AbstractModel.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Notations.
Require Import Hafnium.Concrete.PageTablesWf.
Require Import Hafnium.Concrete.Parameters.
Require Import Hafnium.Concrete.PointerLocations.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.ArchMM.
Require Import Hafnium.Concrete.Assumptions.Constants.
Require Import Hafnium.Concrete.Assumptions.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Mpool.
Require Import Hafnium.Concrete.Assumptions.PageTables.
Require Import Hafnium.Concrete.MM.Datatypes.

(*** This file defines the state type for the concrete model and relates it to
     the abstract state. ***)

Record concrete_state :=
  {
    (* representation of the state of page tables in memory *)
    ptable_deref : ptable_pointer -> mm_page_table;
    api_page_pool : mpool;
  }.

Definition update_deref (deref : ptable_pointer -> mm_page_table)
           (ptr : ptable_pointer) (t : mm_page_table)
  : ptable_pointer -> mm_page_table :=
  (fun ptr' =>
     if ptable_pointer_eq_dec ptr ptr'
     then t
     else deref ptr').

Definition reassign_pointer
           (s : concrete_state) (ptr : ptable_pointer) (t : mm_page_table)
  : concrete_state :=
  {|
    ptable_deref := update_deref s.(ptable_deref) ptr t;
    api_page_pool := s.(api_page_pool);
  |}.

Definition is_valid {cp : concrete_params} (s : concrete_state) : Prop :=
  locations_exclusive s.(ptable_deref) s.(api_page_pool)
  /\ Forall (root_ptable_wf s.(ptable_deref) Stage2) (map vm_ptable vms)
  /\ root_ptable_wf s.(ptable_deref) Stage1 hafnium_ptable
.

Definition vm_find {cp : concrete_params} (vid : nat) : option vm :=
  find (fun v => (v.(vm_id) =? vid)) vms.

Definition stage2_mode_has_value
           (s : concrete_state) (v : vm) (a : paddr_t)
           (mode_flag : N) (expected_value : bool) : Prop :=
  let attrs := page_attrs s.(ptable_deref) (vm_ptable v) Stage2 a.(pa_addr) in
  let mode := arch_mm_stage2_attrs_to_mode attrs in
  let flag_set := ((mode & mode_flag) != 0)%N in
  flag_set = expected_value.

Definition vm_page_valid {cp : concrete_params}
           (s : concrete_state) (v : vm) (a : paddr_t) : Prop :=
  stage2_mode_has_value s v a MM_MODE_INVALID false.

Definition haf_page_valid
           {cp : concrete_params} (s : concrete_state) (a : paddr_t) : Prop :=
  let attrs := page_attrs s.(ptable_deref) hafnium_ptable Stage1 a.(pa_addr) in
  (N.land attrs PTE_VALID <> 0)%N.

Definition vm_page_owned {cp : concrete_params}
           (s : concrete_state) (v : vm) (a : paddr_t) : Prop :=
  stage2_mode_has_value s v a MM_MODE_UNOWNED false.

(* Stage-1 attributes don't have a specific bit for "owned". However, the set of
   pages owned by Hafnium doesn't change over the course of the program, so we
   can get it from the starting parameters. *)
Definition haf_page_owned
           {ap : @abstract_state_parameters paddr_t nat}
           (s : concrete_state) (a : paddr_t) : Prop :=
  hafnium_reserved a = true.

Arguments owned_by {_} {_} _.
Arguments accessible_by {_} {_} _.
Definition represents
           {cp : concrete_params}
           {ap : abstract_state_parameters}
           (abst : @abstract_state paddr_t nat)
           (conc : concrete_state) : Prop :=
  is_valid conc
  /\ (forall (vid : nat) (a : paddr_t),
         address_wf (pa_addr a) Stage2 ->
         (In (inl vid) (abst.(accessible_by) a) <->
          (exists v : vm,
              vm_find vid = Some v /\ conc.(vm_page_valid) v a)))
  /\ (forall (a : paddr_t),
         address_wf (pa_addr a) Stage1 ->
         (In (inr hid) (abst.(accessible_by) a) <-> conc.(haf_page_valid) a))
  /\ (forall (vid : nat) (a : paddr_t),
         address_wf (pa_addr a) Stage2 ->
         (In (inl vid) (abst.(owned_by) a) <->
          (exists v : vm,
              vm_find vid = Some v /\ conc.(vm_page_owned) v a)))
  /\ (forall (a : paddr_t),
         address_wf (pa_addr a) Stage1 ->
         (In (inr hid) (abst.(owned_by) a) <-> conc.(haf_page_owned) a))
.
Definition represents_valid
           {ap : abstract_state_parameters}
           {cp : concrete_params}
           (abst : @abstract_state paddr_t nat)
           (conc : concrete_state) : Prop :=
  represents abst conc
  /\ AbstractModel.is_valid
       (addr_eq_dec:=paddr_t_eq_dec) (vm_id_eq_dec:=Nat.eq_dec) abst.

Definition abstract_state_equiv
           (s1 s2 : @abstract_state paddr_t nat) : Prop :=
  (forall a, s1.(owned_by) a = s2.(owned_by) a)
  /\ (forall e a,
         In e (s1.(accessible_by) a) <-> In e (s2.(accessible_by) a)).
