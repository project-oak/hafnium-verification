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
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Util.Tactics.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.ArchMM.
Require Import Hafnium.Concrete.Assumptions.Constants.
Require Import Hafnium.Concrete.Assumptions.Datatypes.
Require Import Hafnium.Concrete.Assumptions.PageTables.
Require Import Hafnium.Concrete.MM.Datatypes.

(* states that a table has the right number of entries at every level and doesn't
   exceed the maximum number of levels *)
(* TODO : could add max_block_level to this, and get the proof that tables don't
   have blocks above level 2 *)
Inductive page_table_wf (deref : ptable_pointer -> mm_page_table) (s : Stage)
  : mm_page_table -> nat -> Prop :=
| page_table_wf_last_level :
    (* no table entries at next level down *)
    forall (entries : list pte_t) (level : nat),
      length entries = MM_PTE_PER_PAGE ->
      level < max_level s ->
      Forall (fun pte => arch_mm_pte_is_table pte level = false) entries ->
      page_table_wf deref s {| entries := entries |} level
| page_table_wf_step :
    (* well-formed if the level below is also *)
    forall (entries : list pte_t) (level : nat),
      length entries = MM_PTE_PER_PAGE ->
      level <= max_level s ->
      Forall (fun pte =>
                arch_mm_pte_is_table pte (S level) = true ->
                let next_ptr := ptable_pointer_from_address
                                  (arch_mm_table_from_pte pte (S level)) in
                let next_table := deref next_ptr in
                page_table_wf deref s next_table level) entries ->
      page_table_wf deref s {| entries := entries |} (S level)
.

Definition root_ptable_wf deref (s : Stage) (root_ptable : mm_ptable) : Prop :=
  let root_tables := ptr_from_va (va_from_pa (root root_ptable)) in
  (length root_tables = root_table_count s
   /\ Forall
        (fun ptr => page_table_wf deref s (deref ptr) (max_level s))
        root_tables).

Definition address_wf (a : uintpaddr_t) (s : Stage) : Prop :=
  (forall level, level <= max_level s -> get_index s level a < MM_PTE_PER_PAGE)
  /\ (get_index s (max_level s + 1) a < root_table_count s).

Lemma page_lookup'_ok deref s a :
  forall level t,
    address_wf a s ->
    page_table_wf deref s t (pred level) ->
    0 < level <= max_level s + 1->
    page_lookup' deref a t level s <> None.
Proof.
  induction level; [|destruct (Nat.eq_dec level 0)]; basics;
    match goal with
    | H : address_wf _ _ |- _ => pose proof H; cbv [address_wf] in H
    end;
    repeat match goal with
           | _ => progress basics
           | _ => progress cbn [page_lookup']; cbv [get_entry]
           | _ => progress cbn [Datatypes.entries] in *
           | _ => progress rewrite <-pred_Sn in *
           | H : page_table_wf _ _ _ 0 |- _ => invert H
           | H : page_table_wf _ _ _ ?lvl
             |- page_table_wf _ _ _ (Nat.pred ?lvl) => invert H
           | H : (forall level, _ -> get_index _ level _ < _)
             |- context [get_index _ ?lvl _] => specialize (H lvl ltac:(solver))
           | H : Forall ?P ?ls, H' : In ?x ?ls |- _ =>
             rewrite Forall_forall in H; pose proof H; specialize (H _ H')
           | H : nth_error _ _ = None |- _ => apply nth_error_None in H
           | H : nth_error _ _ = Some _ |- _ => apply nth_error_In in H
           | _ => apply IHlevel
           | H : page_table_wf _ _ _ _ |- _ =>
             invert H; basics; cbn [Datatypes.entries] in *; solver
           | _ => break_match
           | _ => solver
           end.
Qed.

Lemma page_lookup_ok deref root_ptable s a :
  address_wf a s ->
  root_ptable_wf deref s root_ptable ->
  page_lookup deref root_ptable s a <> None.
Proof.
  cbv [page_lookup root_ptable_wf address_wf]; basics.
  match goal with
  | H : ?i < ?l, H' : length ?ls = ?l |- context [nth_error ?ls ?i] =>
    pose proof H; rewrite <-H', <-nth_error_Some in H
  end.
  break_match; [|solver].
  match goal with
  | H : Forall _ ?ls, H' : nth_error ?ls ?i = Some _ |- _ =>
    rewrite Forall_forall in H;
      specialize (H _ (nth_error_In _ _ H'))
  end.
  rewrite Nat.add_1_r.
  apply page_lookup'_ok;
    cbv [address_wf]; basics; try solver.
Qed.
