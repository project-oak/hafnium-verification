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

  Inductive pointer_location (ppool : mpool) : Type :=
  | table_loc : mm_ptable -> list nat -> pointer_location ppool
  | mpool_loc : pointer_location ppool
  .

  Definition pointer_location_eq_dec
             (ppool : mpool) (loc1 loc2 : pointer_location ppool)
    : { loc1 = loc2 } + { loc1 <> loc2 }.
  Proof.
    destruct loc1, loc2;
    repeat match goal with
           | p : mm_ptable |- _ => destruct p
           | r1 : paddr_t, r2 : paddr_t |- _ =>
             destruct (paddr_t_eq_dec r1 r2); [ subst | right; congruence ]
           | l1 : list nat, l2 : list nat |- _ =>
             destruct (list_eq_dec Nat.eq_dec l1 l2); [ subst | right; congruence ]
           | _ => right; congruence
           | _ => left; congruence
           end.
  Defined.

  (* This section includes some definitions which use information from the
     concrete parameters *)
  Section with_concrete_params.
    Context (root_tables : list mm_ptable) (ppool : mpool).

    Inductive has_location : ptable_pointer -> pointer_location ppool -> Prop :=
    | has_table_loc :
        forall root_ptable idxs ptr,
          In root_ptable root_tables ->
          In idxs (index_sequences_to_pointer ptr root_ptable) ->
          has_location ptr (table_loc ppool root_ptable idxs)
    | has_mpool_loc :
        forall ptr,
          mpool_contains ppool ptr ->
          has_location ptr (mpool_loc ppool)
    .

    (* TODO: just guessing that this might come in handy; remove if unused *)
    Lemma table_locations_exclusive ptr1 ptr2 root_ptable idxs :
      has_location ptr1 (table_loc ppool root_ptable idxs) ->
      has_location ptr2 (table_loc ppool root_ptable idxs) ->
      ptr1 = ptr2.
    Admitted.

    (* every ptable_pointer has at most one location *)
    Definition locations_exclusive : Prop :=
      forall ptr loc1 loc2,
        has_location ptr loc1 -> has_location ptr loc2 -> loc1 = loc2.
  End with_concrete_params.
End PointerLocations.
