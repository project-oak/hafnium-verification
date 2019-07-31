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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.Lists.List.
Require Import Hafnium.AbstractModel.
Require Import Hafnium.Concrete.State.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Notations.
Require Import Hafnium.Concrete.PointerLocations.
Require Import Hafnium.Util.List.
Require Import Hafnium.Util.Tactics.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.ArchMM.
Require Import Hafnium.Concrete.Assumptions.Constants.
Require Import Hafnium.Concrete.Assumptions.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Mpool.
Require Import Hafnium.Concrete.Assumptions.PageTables.
Require Import Hafnium.Concrete.MM.Datatypes.

(*** This file contains correctness proofs about the relationship between
     concrete and abstract states. ***)

Section Proofs.
  Context {ap : @abstract_state_parameters paddr_t nat}
          {cp : concrete_params}.

  (* if two concrete states are equivalent and an abstract state represents one
     of them, then it also represents the other. *)
  Lemma represents_proper abst conc conc' :
    (forall ptr, conc.(ptable_deref) ptr = conc'.(ptable_deref) ptr) ->
    (conc.(api_page_pool) = conc'.(api_page_pool)) ->
    represents abst conc ->
    represents abst conc'.
  Admitted.

  (* if two abstract states are equivalent and one represents a concrete state,
     then the other also represents that concrete state. *)
  Lemma represents_proper_abstr abst abst' conc :
    abstract_state_equiv abst abst' ->
    represents abst conc ->
    represents abst' conc.
  Admitted.

  (* [represents] includes [is_valid] as one of its conditions *)
  Lemma represents_valid_concrete conc : (exists abst, represents abst conc) -> is_valid conc.
  Proof. cbv [represents]; basics; auto. Qed.
  Hint Resolve represents_valid_concrete.

  (* [abstract_state_equiv] is reflexive *)
  Lemma abstract_state_equiv_refl abst : abstract_state_equiv abst abst.
  Proof. cbv [abstract_state_equiv]. solver. Qed.
  Hint Resolve abstract_state_equiv_refl.

  (* [abstract_state_equiv] is transitive *)
  Lemma abstract_state_equiv_trans abst1 abst2 abst3 :
    abstract_state_equiv abst1 abst2 ->
    abstract_state_equiv abst2 abst3 ->
    abstract_state_equiv abst1 abst3.
  Proof.
    cbv [abstract_state_equiv].
    basics; try solver.
    match goal with
    | H : context [_ <-> _] |- _ => rewrite H; solver
    end.
  Qed.

  (* if the new table is the same as the old, abstract state doesn't change *)
  Lemma reassign_pointer_noop_represents conc ptr t abst :
    conc.(ptable_deref) ptr = t ->
    represents abst conc <->
    represents abst (conc.(reassign_pointer) ptr t).
  Proof.
    repeat match goal with
           | _ => progress basics
           | _ => progress cbn [reassign_pointer ptable_deref]
           | |- _ <-> _ => split
           | _ => break_match
           | _ => solver
           | _ => eapply represents_proper;
                    [ | | solve[eauto] ]; eauto; [ ]
           end.
  Qed.

  Fixpoint pointer_in_table
             (deref : ptable_pointer -> mm_page_table) (ptr : ptable_pointer)
             (t : mm_page_table) (level : nat) : Prop :=
    match level with
    | 0 => False
    | S level' =>
      Exists
        (fun pte =>
           if arch_mm_pte_is_table pte level
           then
             let next_t_ptr :=
                 ptable_pointer_from_address (arch_mm_table_from_pte pte level) in
             if ptable_pointer_eq_dec ptr next_t_ptr
             then True
             else pointer_in_table deref ptr (deref next_t_ptr) level'
           else False)
        t.(entries)
    end.

  Definition abstract_change_attrs (abst : abstract_state)
             (a : paddr_t) (e : entity_id) (owned valid : bool) :=
    let eq_dec := @entity_id_eq_dec _ Nat.eq_dec in
    {|
      accessible_by :=
        (fun a' =>
           let prev := abst.(accessible_by) a' in
           if paddr_t_eq_dec a a'
           then if valid
                then nodup eq_dec (e :: prev)
                else remove eq_dec e prev
          else prev);
      owned_by :=
        (fun a' =>
           let prev := abst.(owned_by) a' in
           if paddr_t_eq_dec a a'
           then if owned
                then nodup eq_dec (e :: prev)
                else remove eq_dec e prev
           else prev)
    |}.

  (* indices_from_address starts with the index of the root table in the list of
     root tables (0 if there's only one) and then gives the index in the table at
     [max_level]. The length of this sequence of indices is therefore
     [max_level + 2], because it's [0..(max_level + 1)] *inclusive*. *)
  Definition indices_from_address (a : uintpaddr_t) (stage : Stage) : list nat :=
    map (fun lvl => get_index stage lvl a) (rev (seq 0 (S (S (max_level stage))))).

  Definition address_matches_indices (a : uintpaddr_t) (idxs : list nat) (stage : Stage) : Prop :=
    firstn (length idxs) (indices_from_address a stage) = idxs.

  Definition address_matches_indices_bool (a : uintpaddr_t) (idxs : list nat) (stage : Stage) : bool :=
    forallb (fun '(x,y) => x =? y) (combine (indices_from_address a stage) idxs).

  Definition addresses_under_pointer_in_range
             (deref : ptable_pointer -> mm_page_table)
             (ptr : ptable_pointer) (root_ptable : mm_ptable)
             (begin end_ : uintvaddr_t) (stage : Stage) : list paddr_t :=
    let vrange := map N.of_nat (seq (N.to_nat begin) (N.to_nat (end_ - begin))) in
    let prange := map (fun va => pa_from_va (va_init va)) vrange in
    let paths := index_sequences_to_pointer deref ptr root_ptable stage in
    filter
      (fun a => existsb (fun p => address_matches_indices_bool (pa_addr a) p stage) paths) prange.

  Definition abstract_reassign_pointer_for_entity
             (abst : abstract_state) (conc : concrete_state)
             (ptr : ptable_pointer) (owned valid : bool)
             (e : entity_id) (root_ptable : mm_ptable)
             (begin end_ : uintvaddr_t) : abstract_state :=
    let stage := match e with
                 | inl _ => Stage2
                 | inr _ => Stage1
                 end in
    fold_right
      (fun pa abst =>
         abstract_change_attrs abst pa e owned valid)
      abst
      (addresses_under_pointer_in_range
         conc.(ptable_deref) ptr root_ptable begin end_ stage).

  Definition owned_from_attrs (attrs : attributes) (stage : Stage) : bool :=
    match stage with
    | Stage1 =>
      let mode := arch_mm_stage1_attrs_to_mode attrs in
      let unowned := ((mode & MM_MODE_UNOWNED) != 0)%N in
      negb unowned
    | Stage2 =>
      let mode := arch_mm_stage2_attrs_to_mode attrs in
      let unowned := ((mode & MM_MODE_UNOWNED) != 0)%N in
      negb unowned
    end.

  Definition valid_from_attrs (attrs : attributes) (stage : Stage) : bool :=
    match stage with
    | Stage1 =>
      let mode := arch_mm_stage1_attrs_to_mode attrs in
      let invalid := ((mode & MM_MODE_INVALID) != 0)%N in
      negb invalid
    | Stage2 =>
      let mode := arch_mm_stage2_attrs_to_mode attrs in
      let invalid := ((mode & MM_MODE_INVALID) != 0)%N in
      negb invalid
    end.

  (* Update the abstract state to make everything under the given pointer have
     the provided new owned/valid bits. *)
  Definition abstract_reassign_pointer
             (abst : abstract_state) (conc : concrete_state)
             (ptr : ptable_pointer) (attrs : attributes)
             (begin end_ : uintvaddr_t) : abstract_state :=
    (* first, get the owned/valid bits *)
    let s1_owned := owned_from_attrs attrs Stage1 in
    let s2_owned := owned_from_attrs attrs Stage2 in
    let s1_valid := valid_from_attrs attrs Stage1 in
    let s2_valid := valid_from_attrs attrs Stage2 in

    (* update the state with regard to Hafnium *)
    let abst :=
        abstract_reassign_pointer_for_entity
          abst conc ptr s1_owned s1_valid (inr hid) hafnium_ptable begin end_ in

    (* update the state with regard to each VM *)
    fold_right
      (fun (v : vm) (abst : abstract_state) =>
         abstract_reassign_pointer_for_entity
           abst conc ptr s2_owned s2_valid (inl v.(vm_id)) (vm_ptable v)
           begin end_)
      abst
      vms.

  Definition has_uniform_attrs
             (ptable_deref : ptable_pointer -> mm_page_table)
             (table_loc : list nat)
             (t : mm_page_table) (level : nat) (attrs : attributes)
             (begin end_ : uintvaddr_t) (stage : Stage) : Prop :=
    forall (a : uintvaddr_t) (pte : pte_t),
      address_matches_indices (pa_from_va (va_init a)).(pa_addr) table_loc stage ->
      (begin <= a < end_)%N ->
      level <= max_level stage ->
      page_lookup' ptable_deref a t level stage = Some pte ->
      forall lvl, arch_mm_pte_attrs pte lvl = attrs.

  Definition has_location_in_state conc ptr idxs : Prop :=
    exists root_ptable,
      has_location (ptable_deref conc) (map vm_ptable vms) hafnium_ptable
                   (api_page_pool conc) ptr
                   (table_loc conc.(api_page_pool) root_ptable idxs).

  Lemma reassign_pointer_represents conc ptr t abst idxs stage :
    represents abst conc ->
    has_location_in_state conc ptr idxs ->
    let conc' := conc.(reassign_pointer) ptr t in
    locations_exclusive
      conc.(ptable_deref) (map vm_ptable vms) hafnium_ptable conc.(api_page_pool) ->
    locations_exclusive
      conc'.(ptable_deref) (map vm_ptable vms) hafnium_ptable conc.(api_page_pool) ->
    forall attrs level begin end_,
      has_uniform_attrs
        conc'.(ptable_deref) idxs t level attrs begin end_ stage ->
      represents (abstract_reassign_pointer
                    abst conc ptr attrs begin end_)
                 conc'.
  Proof.
    cbv [reassign_pointer represents is_valid].
    cbv [vm_page_valid haf_page_valid vm_page_owned haf_page_owned].
    cbn [ptable_deref api_page_pool].
    basics; try solver.
    (* TODO: 4 subgoals *)
  Admitted.

  (* if the address range is empty (end_ <= begin), then there can be no
     addresses in that range under the given pointer *)
  Lemma addresses_under_pointer_in_range_empty
        deref ptr root_ptbl begin end_ stage :
    (end_ <= begin)%N ->
    addresses_under_pointer_in_range deref ptr root_ptbl begin end_ stage = nil.
  Proof.
    intros; cbv [addresses_under_pointer_in_range].
    replace (end_ - begin)%N with 0%N by solver.
    reflexivity.
  Qed.

  (* if the address range is empty (end_ <= begin), then the abstract state
     doesn't change *)
  Lemma abstract_reassign_pointer_for_entity_trivial
        abst conc ptr owned valid e root_ptable begin end_ :
    (end_ <= begin)%N ->
    abstract_state_equiv
      abst
      (abstract_reassign_pointer_for_entity
         abst conc ptr owned valid e root_ptable begin end_).
  Proof.
    intros; cbv [abstract_reassign_pointer_for_entity].
    rewrite addresses_under_pointer_in_range_empty by solver.
    cbn [fold_right]; auto.
  Qed.

  (* if the address range is empty (end_ <= begin), then the abstract state
     doesn't change *)
  Lemma abstract_reassign_pointer_trivial abst conc ptr attrs begin end_:
    (end_ <= begin)%N ->
    abstract_state_equiv
      abst
      (abstract_reassign_pointer abst conc ptr attrs begin end_).
  Proof.
    intros; cbv [abstract_reassign_pointer].
    apply fold_right_invariant; intros;
      [ eapply abstract_state_equiv_trans; [eassumption|] | ];
      auto using abstract_reassign_pointer_for_entity_trivial.
  Qed.

  Lemma abstract_reassign_pointer_for_entity_change_concrete
        abst conc conc' ptr owned valid e root_ptr begin end_ :
    index_sequences_to_pointer conc.(ptable_deref) ptr root_ptr
    = index_sequences_to_pointer conc'.(ptable_deref) ptr root_ptr ->
    abstract_reassign_pointer_for_entity
      abst conc ptr owned valid e root_ptr begin end_
    = abstract_reassign_pointer_for_entity
        abst conc' ptr owned valid e root_ptr begin end_.
  Proof.
    cbv beta iota delta [abstract_reassign_pointer_for_entity
                           addresses_under_pointer_in_range].
    intro Heq. rewrite Heq. reflexivity.
  Qed.

  Lemma abstract_reassign_pointer_change_concrete
        abst conc conc' ptr attrs begin_index end_index :
    Forall (fun root =>
              index_sequences_to_pointer conc.(ptable_deref) ptr root
              = index_sequences_to_pointer conc'.(ptable_deref) ptr root)
           all_root_ptables ->
    abstract_reassign_pointer abst conc ptr attrs begin_index end_index
    = abstract_reassign_pointer abst conc' ptr attrs begin_index end_index.
  Proof.
    cbv [abstract_reassign_pointer all_root_ptables].
    repeat match goal with
           | _ => progress basics
           | _ => progress invert_list_properties
           | H : _ |- _ => apply Forall_map in H; rewrite Forall_forall in H
           | _ =>
             rewrite abstract_reassign_pointer_for_entity_change_concrete
               with (conc':=conc') by eauto
           | _ => apply fold_right_ext
           | _ => solve
                    [auto using
                          abstract_reassign_pointer_for_entity_change_concrete]
           end.
  Qed.

  (* has_uniform_attrs doesn't care if we reassign the pointer we started from *)
  (* TODO : fill in preconditions *)
  Lemma has_uniform_attrs_reassign_pointer
        c ptr new_table t level attrs begin end_ idxs stage :
    (* this precondition is so we know c doesn't show up in the new table *)
    is_valid (reassign_pointer c ptr new_table) ->
    has_location_in_state c ptr idxs ->
    has_uniform_attrs (ptable_deref c) idxs t level attrs begin end_ stage ->
    has_uniform_attrs
      (ptable_deref (reassign_pointer c ptr new_table))
      idxs t level attrs begin end_ stage.
  Admitted. (* TODO *)

  Definition no_addresses_in_range deref ptr begin end_ : Prop :=
    Forall
      (fun root_ptable =>
         addresses_under_pointer_in_range deref ptr root_ptable begin end_ Stage2 = nil)
      (map vm_ptable vms)
    /\ addresses_under_pointer_in_range deref ptr hafnium_ptable begin end_ Stage1 = nil.

  (* abstract_reassign_pointer is a no-op if the given tables don't have any
     addresses in range *)
  (* TODO: fill in preconditions; likely needs to know that the table is at the
     right level *)
  Lemma abstract_reassign_pointer_low
        abst conc attrs begin end_ t_ptrs :
    Forall
      (fun ptr => no_addresses_in_range conc.(ptable_deref) ptr begin end_)
      t_ptrs ->
    abstract_state_equiv
      abst
      (fold_left
         (fun abst t_ptr =>
            abstract_reassign_pointer abst conc t_ptr attrs begin end_)
         t_ptrs
         abst).
  Admitted.

  (* we can expand the range to include pointers that are out of range *)
  (* TODO: fill in preconditions; likely needs to know that the table is at the
     right level *)
  Lemma abstract_reassign_pointer_high
        abst conc attrs begin end_ i t_ptrs :
    Forall
      (fun ptr => no_addresses_in_range conc.(ptable_deref) ptr begin end_)
      (skipn i t_ptrs) ->
    abstract_state_equiv
      (fold_left
         (fun abst t_ptr =>
            abstract_reassign_pointer abst conc t_ptr attrs begin end_)
         (firstn i t_ptrs)
         abst)
      (fold_left
         (fun abst t_ptr =>
            abstract_reassign_pointer abst conc t_ptr attrs begin end_)
         t_ptrs
         abst).
  Admitted.
End Proofs.
