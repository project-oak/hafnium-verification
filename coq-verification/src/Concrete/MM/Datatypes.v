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
Require Import Hafnium.Util.List.
Require Import Hafnium.Concrete.Assumptions.Addr.

(*** This file transcribes some datatypes found in mm.h, with original C in
     comments alongside ***)

(*
struct mm_page_table {
	alignas(PAGE_SIZE) pte_t entries[MM_PTE_PER_PAGE];
};
 *)
Record mm_page_table := { entries : list pte_t }.

(*
struct mm_ptable {
	/** Address of the root of the page table. */
	paddr_t root;
};
 *)
Record mm_ptable := { root : paddr_t }.

(* Shortcut definition for replacing the PTE at a given index *)
Definition mm_page_table_replace_entry
           (t : mm_page_table) (pte : pte_t) (index : nat) : mm_page_table :=
  {| entries := set_nth t.(entries) pte index |}.

(* opaque type of PTEs returned by an out-of-bounds access *)
Axiom out_of_bounds_access_pte : pte_t.

(* out-of-bounds accesses to lists of PTEs return out_of_bounds_access_pte *)
Global Instance ptable_pointer_oobe : OutOfBoundsElement pte_t :=
  {| oob_value := out_of_bounds_access_pte |}.
