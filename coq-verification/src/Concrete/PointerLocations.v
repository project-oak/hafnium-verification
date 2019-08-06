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
Require Import Hafnium.Util.List.
Require Import Hafnium.Util.Tactics.

Section PointerLocations.
  Context (ptable_deref : ptable_pointer -> mm_page_table).

  (* We haven't formalized anywhere that pointers don't repeat, so we return a
     list of all locations where the provided pointer exists even though we
     expect there is only one. *)
  Fixpoint index_sequences_to_pointer''
           (ptr : ptable_pointer) (root : ptable_pointer) (level : nat)
    : list (list nat) :=
    match level with
    | 0 => nil
    | S level' =>
      if ptable_pointer_eq_dec root ptr
      then cons nil nil
      else
        let ptable := ptable_deref root in
        flat_map
          (fun index =>
             match get_entry ptable index with
             | Some pte =>
               if arch_mm_pte_is_table pte level
               then
                 let next_root :=
                     ptable_pointer_from_address
                       (arch_mm_table_from_pte pte level) in
                 map
                   (cons index)
                   (index_sequences_to_pointer'' ptr next_root level')
               else nil
             | None => nil
             end)
          (seq 0 (length ptable.(entries)))
    end.
  Fixpoint index_sequences_to_pointer'
           (ptr : ptable_pointer) (root_index : nat)
           (root_ptrs : list ptable_pointer) (stage : Stage) : list (list nat) :=
    match root_ptrs with
    | nil => nil
    | cons root_ptr root_ptrs' =>
      (map (cons root_index)
           (index_sequences_to_pointer'' ptr root_ptr (max_level stage)))
        ++ index_sequences_to_pointer' ptr (S root_index) root_ptrs' stage
    end.
  Definition index_sequences_to_pointer
           (ptr : ptable_pointer) (root_ptable : mm_ptable) (stage : Stage) :=
    index_sequences_to_pointer'
      ptr 0 (ptr_from_va (va_from_pa root_ptable.(root))) stage.

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
    Context (vm_ptables : list mm_ptable) (haf_ptable : mm_ptable) (ppool : mpool).

    Inductive has_location : ptable_pointer -> pointer_location ppool -> Prop :=
    | has_table_loc_stage1 :
        forall idxs ptr,
          In idxs (index_sequences_to_pointer ptr haf_ptable Stage1) ->
          has_location ptr (table_loc ppool haf_ptable idxs)
    | has_table_loc_stage2 :
        forall root_ptable idxs ptr,
          In root_ptable vm_ptables ->
          In idxs (index_sequences_to_pointer ptr root_ptable Stage2) ->
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

  Lemma index_sequences_to_pointer''_root ptr level :
    0 < level ->
    In nil (index_sequences_to_pointer'' ptr ptr level).
  Proof.
    destruct level; [solver|]; intros.
    cbn [index_sequences_to_pointer''].
    break_match; solver.
  Qed.

  Lemma index_sequences_to_pointer'_nth_default root_list stage :
    forall i j k,
      i < length root_list ->
      k = i + j ->
      In (k :: nil)
         (index_sequences_to_pointer'
            (nth_default_oobe root_list i) j root_list stage).
  Proof.
    cbv [nth_default_oobe]. pose proof (max_level_pos stage).
    induction root_list; destruct i; cbn [length index_sequences_to_pointer'];
      repeat match goal with
             | _ => progress basics
             | _ => progress autorewrite with push_nth_default
             | _ => rewrite Nat.add_0_l
             | _ => apply in_or_app
             | _ => left; apply in_map;
                      solve [auto using index_sequences_to_pointer''_root]
             | _ => right; apply IHroot_list; solver
             | _ => solver
             end.
  Qed.
End PointerLocations.
