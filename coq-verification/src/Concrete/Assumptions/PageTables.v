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

(*** This file encodes in Coq how we expect page table lookups to work. It should
     be considered part of the TCB, because the proofs rely on this transcription
     being a correct description of the lookup procedure. ***)

(* index in each level of the page table (highest is root) *)
Axiom index0 : uintpaddr_t -> nat.
Axiom index1 : uintpaddr_t -> nat.
Axiom index2 : uintpaddr_t -> nat.
Axiom index3 : uintpaddr_t -> nat.

(* in-page offset *)
Axiom offset : uintpaddr_t -> nat.

(* if we have a table PTE, we want to extract the address and get a
   ptable_pointer out of it *)
Axiom ptable_pointer_from_address : paddr_t -> ptable_pointer.

Definition get_entry (ptable : mm_page_table) (i : nat) : option pte_t :=
  nth_error ptable.(entries) i.

Definition get_index (level : nat) (a : uintpaddr_t) : nat :=
  match level with
  | 0 => index0 a
  | 1 => index1 a
  | 2 => index2 a
  | 3 => index3 a
  | _ => 0 (* invalid level *)
  end.

(* N.B. the [option] here doesn't mean whether the entry is
   valid/present; rather, the lookup should return [Some] for any
   valid input, but the PTE returned might be absent or invalid. *)
Fixpoint page_lookup'
         (ptable_deref : ptable_pointer -> mm_page_table)
         (a : uintpaddr_t)
         (table : mm_page_table)
         (level : nat)
  : option pte_t :=
  match level with
  | 0 => None
  | S level' =>
    match (get_entry table (get_index level a)) with
    | Some pte =>
      if (arch_mm_pte_is_table pte level)
      then
        (* follow the pointer to the next table *)
        let next_ptr := ptable_pointer_from_address
                          (arch_mm_table_from_pte pte level) in
        let next_table := ptable_deref next_ptr in
        page_lookup' ptable_deref a next_table level'
      else Some pte
    | None => None
    end
  end.

Definition page_lookup
           (ptable_deref : ptable_pointer -> mm_page_table)
           (root_ptable : ptable_pointer)
           (a : uintpaddr_t) : option pte_t :=
  page_lookup' ptable_deref a (ptable_deref root_ptable) 4.
