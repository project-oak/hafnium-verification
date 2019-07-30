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
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.ArchMM.
Require Import Hafnium.Concrete.Assumptions.Constants.
Require Import Hafnium.Concrete.Assumptions.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Mpool.
Require Import Hafnium.Concrete.Assumptions.PageTables.
Require Import Hafnium.Concrete.MM.Datatypes.

Section PointerLocations.
  Context (ptable_deref : ptable_pointer -> mm_page_table).

  (* We haven't formalized anywhere that pointers don't repeat, so we return a
     list of all locations where the provided pointer exists even though we
     expect there is only one. *)
  Fixpoint index_sequences_to_pointer''
           (ptr : ptable_pointer) (root : ptable_pointer) (lvls_to_go : nat)
    : list (list nat) :=
    match lvls_to_go with
    | 0 => nil
    | S lvls_to_go' =>
      let lvl := 4 - lvls_to_go in
      if ptable_pointer_eq_dec root ptr
      then cons nil nil
      else
        let ptable := ptable_deref root in
        flat_map
          (fun index =>
             match get_entry ptable index with
             | Some pte =>
               if arch_mm_pte_is_table pte lvl
               then
                 let next_root :=
                     ptable_pointer_from_address
                       (arch_mm_table_from_pte pte lvl) in
                 map
                   (cons index)
                   (index_sequences_to_pointer'' ptr next_root lvls_to_go')
               else nil
             | None => nil
             end)
          (seq 0 (length ptable.(entries)))
    end.
  Fixpoint index_sequences_to_pointer'
           (ptr : ptable_pointer) (root_index : nat)
           (root_ptrs : list ptable_pointer) : list (list nat) :=
    match root_ptrs with
    | nil => nil
    | cons root_ptr root_ptrs' =>
      (map (cons root_index)
           (index_sequences_to_pointer'' ptr root_ptr 4))
        ++ index_sequences_to_pointer' ptr (S root_index) root_ptrs'
    end.
  Definition index_sequences_to_pointer
           (ptr : ptable_pointer) (root_ptable : mm_ptable) :=
    index_sequences_to_pointer'
      ptr 0 (ptr_from_va (va_from_pa root_ptable.(root))).
End PointerLocations.
