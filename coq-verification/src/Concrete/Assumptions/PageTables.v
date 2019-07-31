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
Require Import Coq.NArith.BinNat.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Notations.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.ArchMM.
Require Import Hafnium.Concrete.Assumptions.Constants.
Require Import Hafnium.Concrete.Assumptions.Datatypes.
Require Import Hafnium.Concrete.MM.Datatypes.

(*** This file encodes in Coq how we expect page table lookups to work. It should
     be considered part of the TCB, because the proofs rely on this transcription
     being a correct description of the lookup procedure. ***)

(* if we have a table PTE, we want to extract the address and get a
   ptable_pointer out of it *)
Axiom ptable_pointer_from_address : paddr_t -> ptable_pointer.

Definition get_entry (ptable : mm_page_table) (i : nat) : option pte_t :=
  nth_error ptable.(entries) i.

Axiom get_stage1_index : nat (* level *) -> uintpaddr_t -> nat.
Axiom get_stage2_index : nat (* level *) -> uintpaddr_t -> nat.

(* enum for stages 1 and 2 *)
Inductive Stage : Type := Stage1 | Stage2.

Definition get_index (s : Stage) (level : nat) (a : uintpaddr_t) : nat :=
  match s with
  | Stage1 => get_stage1_index level a
  | Stage2 => get_stage2_index level a
  end.

Definition max_level (s : Stage) : nat :=
  match s with
  | Stage1 => arch_mm_stage1_max_level
  | Stage2 => arch_mm_stage2_max_level
  end.

Definition is_stage1 (s : Stage) : bool :=
  match s with
  | Stage1 => true
  | Stage2 => false
  end.

Axiom stage1_index_of_uintvaddr :
  forall (a : uintvaddr_t) (level : nat),
    (* level offset for uintvaddr_t *)
    let offset := (PAGE_BITS + level * PAGE_LEVEL_BITS)%N in
    (* convert a to uintpaddr_t *)
    let b : uintpaddr_t := pa_addr (pa_from_va (va_init a)) in
    level <= S (max_level Stage1) ->
    get_stage1_index level b = N.to_nat ((a / 2 ^ offset) mod 2 ^ PAGE_LEVEL_BITS).

Axiom stage2_index_of_uintvaddr :
  forall (a : uintvaddr_t) (level : nat),
    (* level offset for uintvaddr_t *)
    let offset := (PAGE_BITS + level * PAGE_LEVEL_BITS)%N in
    (* convert a to uintpaddr_t *)
    let b : uintpaddr_t := pa_addr (pa_from_va (va_init a)) in
    level <= S (max_level Stage2) ->
    get_stage2_index level b = N.to_nat ((a / 2 ^ offset) mod 2 ^ PAGE_LEVEL_BITS).

(* TODO: this limits level to [S (max_level stage)] to allow for indices in
   top-level lists of root tables -- is that the correct behavior? *)
Lemma index_of_uintvaddr (a : uintvaddr_t) (level : nat) stage :
    let offset := (PAGE_BITS + level * PAGE_LEVEL_BITS)%N in
    let b : uintpaddr_t := pa_addr (pa_from_va (va_init a)) in
    level <= S (max_level stage) ->
    get_index stage level b = N.to_nat ((a / 2 ^ offset) mod 2 ^ PAGE_LEVEL_BITS).
Proof.
  destruct stage; cbv [get_index];
    auto using stage1_index_of_uintvaddr, stage2_index_of_uintvaddr.
Qed.

(* N.B. the [option] here doesn't mean whether the entry is
   valid/present; rather, the lookup should return [Some] for any
   valid input, but the PTE returned might be absent or invalid. *)
Fixpoint page_lookup'
         (ptable_deref : ptable_pointer -> mm_page_table)
         (a : uintpaddr_t)
         (table : mm_page_table)
         (level : nat)
         (s : Stage)
  : option pte_t :=
  match level with
  | 0 => None
  | S level' =>
    match (get_entry table (get_index s level a)) with
    | Some pte =>
      if (arch_mm_pte_is_table pte level)
      then
        (* follow the pointer to the next table *)
        let next_ptr := ptable_pointer_from_address
                          (arch_mm_table_from_pte pte level) in
        let next_table := ptable_deref next_ptr in
        page_lookup' ptable_deref a next_table level' s
      else Some pte
    | None => None
    end
  end.

Definition page_lookup
           (ptable_deref : ptable_pointer -> mm_page_table)
           (root_ptable : mm_ptable) (s : Stage)
           (a : uintpaddr_t) : option pte_t :=
  let root_tables := ptr_from_va (va_from_pa (root root_ptable)) in
  let index := get_index s (max_level s + 1) a in
  let table_ptr := nth_default null_pointer root_tables index in
  page_lookup' ptable_deref a (ptable_deref table_ptr) (max_level s) s.
