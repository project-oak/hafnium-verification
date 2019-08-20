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
Require Import Hafnium.Concrete.Parameters.
Require Import Hafnium.Concrete.State.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Notations.
Require Import Hafnium.Concrete.PageTablesWf.
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
          {cp : concrete_params} {cp_valid : params_valid}.

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
  Proof.
    intro Hequiv. destruct Hequiv as [Hown Haccess].
    cbv [represents]; basics; rewrite <-?Hown, <-?Haccess; solver.
  Qed.

  (* [represents] includes [is_valid] as one of its conditions *)
  Lemma represents_valid_concrete conc : (exists abst, represents abst conc) -> is_valid conc.
  Proof. cbv [represents]; basics; auto. Qed.
  Hint Resolve represents_valid_concrete.

  (* [abstract_state_equiv] is reflexive *)
  Lemma abstract_state_equiv_refl abst : abstract_state_equiv abst abst.
  Proof. cbv [abstract_state_equiv]. solver. Qed.
  Hint Resolve abstract_state_equiv_refl.

  (* [abstract_state_equiv] is symmetric *)
  Lemma abstract_state_equiv_sym abst1 abst2 :
    abstract_state_equiv abst1 abst2 ->
    abstract_state_equiv abst2 abst1.
  Proof.
    cbv [abstract_state_equiv].
    basics; try solver.
    match goal with
    | H : context [_ <-> _] |- _ => rewrite H; solver
    end.
  Qed.
  Hint Resolve abstract_state_equiv_sym.

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
           | _ => progress cbv [update_deref]
           | |- _ <-> _ => split
           | _ => break_match
           | _ => solver
           | _ => eapply represents_proper;
                    [ | | solve[eauto] ]; eauto; [ ]
           end.
  Qed.

  Lemma hafnium_ptable_nodup : ~ In hafnium_ptable (map vm_ptable vms).
  Proof.
    invert cp_valid; cbv [all_root_ptables] in *.
    invert_list_properties; solver.
  Qed.
  Hint Resolve hafnium_ptable_nodup.

  Definition vm_eq_dec (v1 v2 : vm) : {v1 = v2} + {v1 <> v2}.
  Proof.
    repeat match goal with
           | _ => progress subst
           | x : vm |- _ => destruct x
           | x : mm_ptable |- _ => destruct x
           | _ => right; congruence
           | _ => left; congruence
           | x : nat, y : nat |- _ => destruct (Nat.eq_dec x y)
           | x : paddr_t, y : paddr_t |- _ => destruct (paddr_t_eq_dec x y)
           end.
  Defined.

  Local Ltac destruct_vm_eq :=
    match goal with
    | x : vm, y : vm |- _ =>
      progress match goal with
               | H : x <> y |- _ => idtac
               | H : y <> x |- _ => idtac
               | _ => destruct (vm_eq_dec x y); basics
               end
    end.

  Local Ltac pose_in_vm_ptable_map :=
    repeat match goal with
           | H : In ?v vms |- _ =>
             progress match goal with
                      | H : In (vm_ptable v) (map vm_ptable vms) |- _ => idtac
                      | _ => assert (In (vm_ptable v) (map vm_ptable vms)) by eauto using in_map
                      end
           end.

  Lemma vm_ptable_nodup v1 v2 :
    In v1 vms -> In v2 vms -> v1 <> v2 -> vm_ptable v1 <> vm_ptable v2.
  Proof.
    invert cp_valid; cbv [all_root_ptables] in *; basics.
    pose_in_vm_ptable_map; invert_list_properties.
    eapply NoDup_map_neq; eauto.
  Qed.

  Lemma vm_ptable_in_all v : In v vms -> In (vm_ptable v) all_root_ptables.
  Proof. cbv [all_root_ptables]; auto using in_map. Qed.

  Lemma hafnium_neq_vm_ptable v : In v vms -> hafnium_ptable <> vm_ptable v.
  Proof.
    pose proof hafnium_ptable_nodup.
    basics; pose_in_vm_ptable_map.
    intro; solver.
  Qed.

  Lemma vm_find_Some v : In v vms -> vm_find (vm_id v) = Some v.
  Proof.
    cbv [vm_find].
    repeat match goal with
           | _ => progress basics
           | _ => inversion_bool
           | _ => destruct_vm_eq
           | H : _ |- _ => apply find_some in H
           | H : context [find ?f] |- _ => eapply (find_none f) in H; [|solver]
           | |- context [find ?f ?l] => case_eq (find f l)
           | H : ?v1 <> ?v2 |- _ =>
             assert (vm_id v1 <> vm_id v2)
               by eauto using NoDup_map_neq, no_duplicate_ids; solver
           | _ => solver
           end.
  Qed.
  Hint Resolve vm_find_Some.

  Lemma vm_find_sound v vid : vm_find vid = Some v -> vm_id v = vid.
  Proof.
    cbv [vm_find].
    repeat match goal with
           | _ => progress basics
           | _ => inversion_bool
           | H : _ |- _ => apply find_some in H
           | _ => solver
           end.
  Qed.
  Hint Resolve vm_find_sound.

  Lemma vm_find_unique_entity v1 v2 vid :
    vm_find vid = Some v2 ->
    In v1 vms ->
    v1 <> v2 ->
    ~ (@eq entity_id (inl vid) (inl (vm_id v1))).
  Proof.
    cbv [vm_find].
    repeat match goal with
           | _ => progress basics
           | _ => inversion_bool
           | H : _ |- _ => apply find_some in H
           | |- inl _ <> inl _ =>
             let H := fresh in intro H; invert H
           | H : ?v1 <> ?v2 |- _ =>
             assert (vm_id v1 <> vm_id v2)
               by eauto using NoDup_map_neq, no_duplicate_ids; solver
           | _ => solver
           end.
  Qed.
  Hint Resolve vm_find_unique_entity.

  Lemma vm_find_In vid v : vm_find vid = Some v -> In v vms.
  Proof.
    cbv [vm_find].
    repeat match goal with
           | _ => progress basics
           | _ => inversion_bool
           | H : _ |- _ => apply find_some in H
           | _ => solver
           end.
  Qed.
  Hint Resolve vm_find_In.


  Lemma index_sequences_update_deref'' deref ptr t level :
    forall root_ptr idxs,
      In idxs (index_sequences_to_pointer'' deref ptr root_ptr level) ->
      In idxs (index_sequences_to_pointer''
                 (update_deref deref ptr t) ptr root_ptr level).
  Proof.
    cbv [update_deref]; induction level; cbn [index_sequences_to_pointer'']; [ solver | basics ].
    repeat break_match; basics; try solver; [ ].
    rewrite in_flat_map in *.
    basics. eexists; split; [eassumption|].
    repeat break_match; basics; try solver; [ ].
    rewrite in_map_iff in *. basics.
    eexists; eauto.
  Qed.

  Lemma index_sequences_update_deref' deref ptr t stage :
    forall root_ptrs i idxs,
      In idxs (index_sequences_to_pointer' deref ptr i root_ptrs stage) ->
      In idxs (index_sequences_to_pointer'
                 (update_deref deref ptr t) ptr i root_ptrs stage).
  Proof.
    induction root_ptrs; cbn [index_sequences_to_pointer']; [ solver | basics ].
    repeat match goal with
           | _ => progress basics
           | _ => rewrite in_app_iff in *
           | _ => rewrite in_map_iff in *
           | _ => rewrite in_cons_iff in *
           | _ => solver
           | _ => left; eexists; split;
                    solve [eauto using index_sequences_update_deref'']
           end.
  Qed.

  Lemma index_sequences_update_deref deref ptr t root_ptable idxs stage :
    In idxs (index_sequences_to_pointer deref ptr root_ptable stage) ->
    In idxs (index_sequences_to_pointer
               (update_deref deref ptr t) ptr root_ptable stage).
  Proof.
    cbv [index_sequences_to_pointer]; eauto using index_sequences_update_deref'.
  Qed.

  Lemma has_location_update_deref deref ppool ptr t root_ptable idxs :
    has_location deref ptr (table_loc ppool root_ptable idxs) ->
    has_location (update_deref deref ptr t) ptr (table_loc ppool root_ptable idxs).
  Proof.
    inversion 1; basics; constructor; auto using index_sequences_update_deref.
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
             (a : paddr_t) (e : entity_id) (s : Stage) (owned valid : bool) :=
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
        match s with
          | Stage1 => abst.(owned_by) (* if we're modifying stage-1, the owned_by
                                         state can't change; stage-1 tables have
                                         no "owned" bit *)
          | Stage2 =>
            (fun a' =>
               let prev := abst.(owned_by) a' in
               if paddr_t_eq_dec a a'
               then if owned
                    then nodup eq_dec (e :: prev)
                    else remove eq_dec e prev
               else prev)
        end
    |}.

  (* indices_from_address starts with the index of the root table in the list of
     root tables (0 if there's only one) and then gives the index in the table at
     [max_level]. The length of this sequence of indices is therefore
     [max_level + 2], because it's [0..(max_level + 1)] *inclusive*. *)
  Definition indices_from_address (a : uintpaddr_t) (stage : Stage) : list nat :=
    rev (map (fun lvl => get_index stage lvl a) (seq 0 (S (S (max_level stage))))).

  Definition address_matches_indices_bool
             (a : uintpaddr_t) (idxs : list nat) (stage : Stage) : bool :=
    forallb (fun i => get_index stage (max_level stage + 1 - i) a =? nth i idxs 0)
            (seq 0 (length idxs)).

  Definition addresses_under_pointer_in_range
             (deref : ptable_pointer -> mm_page_table)
             (ptr : ptable_pointer) (root_ptable : mm_ptable)
             (begin end_ : uintvaddr_t) (stage : Stage) : list paddr_t :=
    let vrange := map N.of_nat (seq (N.to_nat begin) (N.to_nat (end_ - begin))) in
    let prange := map (fun va => pa_from_va (va_init va)) vrange in
    let paths := index_sequences_to_pointer deref ptr root_ptable stage in
    match paths with
    | nil => (* no paths -> no addresses *) nil
    | path :: _ => (* expects at most one sequence -- prove by locations_exclusive *)
      filter
        (fun a => address_matches_indices_bool (pa_addr a) path stage) prange
    end.

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
         abstract_change_attrs abst pa e stage owned valid)
      abst
      (addresses_under_pointer_in_range
         conc.(ptable_deref) ptr root_ptable begin end_ stage).

  Definition stage2_mode_flag_set (attrs : attributes) (mode_flag : N) : bool :=
    let mode := arch_mm_stage2_attrs_to_mode attrs in
    ((mode & mode_flag) != 0)%N.

  Definition stage1_valid (attrs : attributes) : bool :=
    ((attrs & PTE_VALID) != 0)%N.

  (* Update the abstract state to make everything under the given pointer have
     the provided new owned/valid bits. *)
  Definition abstract_reassign_pointer
             (abst : abstract_state) (conc : concrete_state)
             (ptr : ptable_pointer) (attrs : attributes)
             (begin end_ : uintvaddr_t) : abstract_state :=
    let s1_valid := stage1_valid attrs in
    let s2_valid := negb (stage2_mode_flag_set attrs MM_MODE_INVALID) in
    let s2_owned := negb (stage2_mode_flag_set attrs MM_MODE_UNOWNED) in

    (* Hafnium's stage-1 memory doesn't have an "owned" bit, so that value gets
       ignored; we can pass whatever we want *)
    let abst :=
        abstract_reassign_pointer_for_entity
          abst conc ptr false s1_valid (inr hid) hafnium_ptable begin end_ in

    (* update the state with regard to each VM *)
    fold_right
      (fun (v : vm) (abst : abstract_state) =>
         abstract_reassign_pointer_for_entity
           abst conc ptr s2_owned s2_valid (inl v.(vm_id)) (vm_ptable v)
           begin end_)
      abst
      vms.

  (* equivalent to arch_mm_pte_is_present; says that the attributes either have
     the valid bit set or the stage-2 owned bit set. *)
  Definition attrs_present (attrs : attributes) : bool :=
    (((attrs & PTE_VALID) != 0)%N
     || ((arch_mm_stage2_attrs_to_mode attrs & MM_MODE_UNOWNED) =? 0)%N)%bool.

  (* either the attributes are exactly equivalent, or they are both absent *)
  Definition attrs_equiv (attrs1 attrs2 : attributes) : Prop :=
    attrs1 = attrs2
    \/ (attrs_present attrs1 = false /\ attrs_present attrs2 = false).

  (* N.B. level is the level above the table *)
  Definition has_uniform_attrs
             (ptable_deref : ptable_pointer -> mm_page_table)
             (table_loc : list nat)
             (t : mm_page_table) (level : nat) (attrs : attributes)
             (begin end_ : uintvaddr_t) (stage : Stage) : Prop :=
    forall (a_v : uintvaddr_t),
      (begin <= a_v < end_)%N ->
      let a : uintpaddr_t := pa_addr (pa_from_va (va_init a_v)) in
      address_matches_indices stage a table_loc ->
      level = level_from_indices stage table_loc ->
      attrs_equiv (page_attrs' ptable_deref a t level stage) attrs.

  (* N.B. level is the level above the table *)
  Definition attrs_outside_range_unchanged
             (deref : ptable_pointer -> mm_page_table)
             (table_loc : list nat)
             (t_orig t : mm_page_table) (level : nat)
             (begin end_ : uintvaddr_t) (stage : Stage) : Prop :=
    forall (a_v : uintvaddr_t),
      (a_v < begin \/ end_ <= a_v)%N ->
      let a : uintpaddr_t := pa_addr (pa_from_va (va_init a_v)) in
      address_matches_indices stage a table_loc ->
      level = level_from_indices stage table_loc ->
      page_attrs' deref a t_orig level stage
      = page_attrs' deref a t level stage.

  (* N.B. level is the level above the table *)
  Definition attrs_changed_in_range
             (ptable_deref : ptable_pointer -> mm_page_table)
             (table_loc : list nat)
             (t_orig t : mm_page_table) (level : nat) (attrs : attributes)
             (begin end_ : uintvaddr_t) (stage : Stage) : Prop :=
    has_uniform_attrs ptable_deref table_loc t level attrs begin end_ stage
    /\ attrs_outside_range_unchanged
         ptable_deref table_loc t_orig t level begin end_ stage.

  Definition has_location_in_state conc ptr idxs : Prop :=
    exists root_ptable,
      has_location (ptable_deref conc) ptr
                   (table_loc conc.(api_page_pool) root_ptable idxs).

  Lemma index_sequences_has_location_stage2 deref ppool ptr v :
    In v vms ->
    index_sequences_to_pointer deref ptr (vm_ptable v) Stage2 <> nil ->
    exists idxs,
      has_location deref ptr (table_loc ppool (vm_ptable v) idxs).
  Proof.
    basics.
    match goal with H : ?ls <> nil |- _ =>
                    case_eq ls; [solver | intros idxs ? Hidxs] end.
    exists idxs; constructor; try rewrite Hidxs; eauto using in_map.
  Qed.

  Lemma index_sequences_has_location_stage1 deref ppool ptr :
    index_sequences_to_pointer deref ptr hafnium_ptable Stage1 <> nil ->
    exists idxs,
      has_location deref ptr (table_loc ppool hafnium_ptable idxs).
  Proof.
    basics.
    match goal with H : ?ls <> nil |- _ =>
                    case_eq ls; [solver | intros idxs ? Hidxs] end.
    exists idxs; constructor; try rewrite Hidxs; eauto using in_map.
  Qed.

  Local Ltac two_locations_contradiction :=
    match goal with
    | Hexcl : context [PointerLocations.locations_exclusive],
              Hloc1 : _, Hloc2 : _ |- _ =>
      specialize (Hexcl _ _ _ Hloc1 Hloc2); invert Hexcl
    end.

  Lemma addresses_under_pointer_in_range_pointer_absent
        deref ppool ptr root_ptable begin end_ stage :
    (exists idxs,
        has_location deref ptr (table_loc ppool root_ptable idxs)) ->
    locations_exclusive deref ppool ->
    forall root_ptable2,
      root_ptable <> root_ptable2 ->
      In root_ptable2 all_root_ptables ->
      root_ptable_matches_stage root_ptable2 stage ->
      addresses_under_pointer_in_range
        deref ptr root_ptable2 begin end_ stage = nil.
  Proof.
    cbv [addresses_under_pointer_in_range]; basics.
    case_eq (index_sequences_to_pointer deref ptr root_ptable2 stage);
      [|intros idxs2 ? Hidxs2]; basics.
    { solver. }
    { assert (has_location deref ptr (table_loc ppool root_ptable2 idxs2)).
      { cbv [all_root_ptables root_ptable_matches_stage] in *.
        pose proof hafnium_ptable_nodup.
        invert_list_properties; destruct stage; constructor; try rewrite Hidxs2;
          solver. }
      two_locations_contradiction.
      solver. }
  Qed.

  Lemma abstract_reassign_pointer_noop
        abst conc ptr owned valid begin end_ e root_ptable stage :
    stage = match e with
            | inl _ => Stage2
            | inr _ => Stage1
            end ->
    addresses_under_pointer_in_range
      (ptable_deref conc) ptr root_ptable begin end_ stage = nil ->
    abstract_reassign_pointer_for_entity
      abst conc ptr owned valid e root_ptable begin end_ = abst.
  Proof.
    cbv [abstract_reassign_pointer_for_entity]; intros ? Hnil.
    basics; rewrite Hnil; solver.
  Qed.

  Lemma abstract_reassign_pointer_for_hafnium_noop
        abst conc ptr owned valid begin end_ v ppool :
    In v vms ->
    (exists idxs,
        has_location
          (ptable_deref conc) ptr
          (table_loc ppool (vm_ptable v) idxs)) ->
    locations_exclusive (ptable_deref conc) ppool ->
    abstract_reassign_pointer_for_entity
      abst conc ptr owned valid (inr hid) hafnium_ptable begin end_ = abst.
  Proof.
    cbv [abstract_reassign_pointer_for_entity]; basics.
    pose proof (hafnium_neq_vm_ptable _ ltac:(solver)).
    eapply abstract_reassign_pointer_noop; [ solver | ].
    eapply addresses_under_pointer_in_range_pointer_absent;
      cbv [all_root_ptables]; solver.
  Qed.

  Lemma abstract_reassign_pointer_for_vm_noop
        abst conc ptr owned valid begin end_ v ppool :
    In v vms ->
    (exists idxs,
        has_location
          (ptable_deref conc) ptr
          (table_loc ppool hafnium_ptable idxs)) ->
    locations_exclusive (ptable_deref conc) ppool ->
    abstract_reassign_pointer_for_entity
      abst conc ptr owned valid (inl (vm_id v)) (vm_ptable v) begin end_ = abst.
  Proof.
    cbv [abstract_reassign_pointer_for_entity]; basics.
    pose_in_vm_ptable_map.
    pose proof (hafnium_neq_vm_ptable _ ltac:(solver)).
    eapply abstract_reassign_pointer_noop; [ solver | ].
    eapply addresses_under_pointer_in_range_pointer_absent;
      cbv [all_root_ptables]; try solver.
  Qed.

  Lemma accessible_by_abstract_reassign_pointer_for_entity
        owned valid eid stage addrs :
    stage = (match eid with
             | inl _ => Stage2
             | inr _ => Stage1
             end) ->
    forall abst a e,
      In e
         (accessible_by
            (fold_right
               (fun (pa : paddr_t) (abst : abstract_state) =>
                  abstract_change_attrs abst pa eid stage owned valid)
               abst addrs) a) <->
          (if in_dec paddr_t_eq_dec a addrs
           then
             if valid
             then e = eid \/ In e (accessible_by abst a)
             else e <> eid /\ In e (accessible_by abst a)
           else In e (accessible_by abst a)).
  Proof.
    induction addrs; basics; destruct eid; cbn [fold_right];
      repeat match goal with
             | _ => progress basics
             | _ => progress cbn [accessible_by abstract_change_attrs]
             | _ => progress invert_list_properties
             | _ => rewrite IHaddrs
             | _ => rewrite nodup_In
             | _ => rewrite in_remove_iff
             | _ => rewrite in_cons_iff
             | H : ~ In _ (cons _ _) |- _ => rewrite in_cons_iff in H
             | _ => break_match
             | _ => solver
             | |- _ <-> _ => split
             end.
  Qed.

  Lemma owned_by_abstract_reassign_pointer_for_vm owned valid v addrs :
    forall abst a e,
      In e
         (owned_by
            (fold_right
               (fun (pa : paddr_t) (abst : abstract_state) =>
                  abstract_change_attrs
                    abst pa (inl (vm_id v)) Stage2 owned valid)
               abst addrs) a) <->
          (if in_dec paddr_t_eq_dec a addrs
           then
             if owned
             then e = inl (vm_id v) \/ In e (owned_by abst a)
             else e <> inl (vm_id v) /\ In e (owned_by abst a)
           else In e (owned_by abst a)).
  Proof.
    induction addrs; basics; cbn [fold_right];
      repeat match goal with
             | _ => progress basics
             | _ => progress cbn [owned_by abstract_change_attrs]
             | _ => progress invert_list_properties
             | _ => rewrite IHaddrs
             | _ => rewrite nodup_In
             | _ => rewrite in_remove_iff
             | _ => rewrite in_cons_iff
             | H : ~ In _ (cons _ _) |- _ => rewrite in_cons_iff in H
             | _ => break_match
             | _ => solver
             | |- _ <-> _ => split
             end.
  Qed.

  (* gives the new [accessible_by] value of an address under an abstract state
     with a pointer reassigned, assuming the pointer is in a VM's page table *)
  Lemma accessible_by_abstract_reassign_pointer_stage2
        abst conc ptr attrs begin end_ (a : paddr_t) v ppool :
    (* v is in the vms list *)
    In v vms ->
    (* ptr is located under v's root ptable *)
    (exists idxs,
        has_location
          (ptable_deref conc) ptr
          (table_loc ppool (vm_ptable v) idxs)) ->
    (* ptr is not located anywhere else *)
    locations_exclusive conc.(ptable_deref) ppool ->
    (* list of addresses that changed *)
    let changed_addrs :=
        addresses_under_pointer_in_range
          (ptable_deref conc) ptr (vm_ptable v) begin end_ Stage2 in
    (* new abstract state *)
    let new_abst :=
        abstract_reassign_pointer abst conc ptr attrs begin end_ in
    forall e : entity_id,
      In e (accessible_by new_abst a) <->
      if (in_dec paddr_t_eq_dec a changed_addrs)
      then
        if stage2_mode_flag_set attrs MM_MODE_INVALID
        then e <> inl (vm_id v) /\ In e (accessible_by abst a)
        else e = inl (vm_id v) \/ In e (accessible_by abst a)
      else In e (accessible_by abst a).
  Proof.
    cbv [abstract_reassign_pointer]; basics.
    erewrite abstract_reassign_pointer_for_hafnium_noop by solver.
    erewrite fold_right_single; eauto using NoDup_map_inv, no_duplicate_ids; [ | ].
    { cbv [ abstract_reassign_pointer_for_entity ].
      rewrite accessible_by_abstract_reassign_pointer_for_entity by solver.
      repeat break_match; repeat inversion_bool; solver. }
    { basics.
      cbv [abstract_reassign_pointer_for_entity].
      erewrite addresses_under_pointer_in_range_pointer_absent;
        cbv [root_ptable_matches_stage];
        eauto using vm_ptable_nodup, vm_ptable_in_all, in_map. }
  Qed.

  (* gives the new [accessible_by] value of an address under an abstract state
     with a pointer reassigned, assuming the pointer is in hafnium's table *)
  Lemma accessible_by_abstract_reassign_pointer_stage1
        abst conc ptr attrs begin end_ (a : paddr_t) ppool :
    (* ptr is located under hafnium's root ptable *)
    (exists idxs,
        has_location
          (ptable_deref conc) ptr
          (table_loc ppool hafnium_ptable idxs)) ->
    (* ptr is not located anywhere else *)
    locations_exclusive conc.(ptable_deref) ppool ->
    (* list of addresses that changed *)
    let changed_addrs :=
        addresses_under_pointer_in_range
          (ptable_deref conc) ptr hafnium_ptable begin end_ Stage1 in
    (* new abstract state *)
    let new_abst :=
        abstract_reassign_pointer abst conc ptr attrs begin end_ in
    forall e : entity_id,
      In e (accessible_by new_abst a) <->
      if (in_dec paddr_t_eq_dec a changed_addrs)
      then
        if stage1_valid attrs
        then e = inr hid \/ In e (accessible_by abst a)
        else e <> inr hid /\ In e (accessible_by abst a)
      else In e (accessible_by abst a).
  Proof.
    cbv [abstract_reassign_pointer].
    apply fold_right_invariant_strong; basics.
    { erewrite abstract_reassign_pointer_for_vm_noop; solver. }
    { cbv [ abstract_reassign_pointer_for_entity ].
      rewrite accessible_by_abstract_reassign_pointer_for_entity by solver.
      repeat break_match; repeat inversion_bool; solver. }
  Qed.

  (* gives the new [owned_by] value of an address under an abstract state with a
     pointer reassigned, assuming the pointer is in a VM's page table *)
  Lemma owned_by_abstract_reassign_pointer_stage2
        abst conc ptr attrs begin end_ v (a : paddr_t) ppool :
    (* v is in the vms list *)
    In v vms ->
    (* ptr is located under v's root ptable *)
    (exists idxs,
        has_location
          (ptable_deref conc) ptr
          (table_loc ppool (vm_ptable v) idxs)) ->
    (* ptr is not located anywhere else *)
    locations_exclusive conc.(ptable_deref) ppool ->
    (* list of addresses that changed *)
    let changed_addrs :=
        addresses_under_pointer_in_range
          (ptable_deref conc) ptr (vm_ptable v) begin end_ Stage2 in
    (* new abstract state *)
    let new_abst :=
        abstract_reassign_pointer abst conc ptr attrs begin end_ in
    forall e : entity_id,
      In e (owned_by new_abst a) <->
      if (in_dec paddr_t_eq_dec a changed_addrs)
      then
        if stage2_mode_flag_set attrs MM_MODE_UNOWNED
        then e <> inl (vm_id v) /\ In e (owned_by abst a)
        else e = inl (vm_id v) \/ In e (owned_by abst a)
      else In e (owned_by abst a).
  Proof.
    cbv [abstract_reassign_pointer]; basics.
    erewrite abstract_reassign_pointer_for_hafnium_noop by solver.
    erewrite fold_right_single; eauto using NoDup_map_inv, no_duplicate_ids; [ | ].
    { cbv [ abstract_reassign_pointer_for_entity ].
      rewrite owned_by_abstract_reassign_pointer_for_vm.
      repeat break_match; repeat inversion_bool; solver. }
    { basics.
      cbv [abstract_reassign_pointer_for_entity].
      erewrite addresses_under_pointer_in_range_pointer_absent;
        cbv [root_ptable_matches_stage];
        eauto using vm_ptable_nodup, vm_ptable_in_all, in_map. }
  Qed.

  (* gives the new [owned_by] value of an address under an abstract state with a
     pointer reassigned, assuming the pointer is in hafnium's table *)
  Lemma owned_by_abstract_reassign_pointer_stage1
        abst conc ptr attrs begin end_ (a : paddr_t) ppool :
    (* ptr is located under hafnium's root ptable *)
    (exists idxs,
        has_location (ptable_deref conc) ptr
          (table_loc ppool hafnium_ptable idxs)) ->
    (* ptr is not located anywhere else *)
    locations_exclusive conc.(ptable_deref) ppool ->
    (* list of addresses that changed *)
    let changed_addrs :=
        addresses_under_pointer_in_range
          (ptable_deref conc) ptr hafnium_ptable begin end_ Stage1 in
    (* new abstract state *)
    let new_abst :=
        abstract_reassign_pointer abst conc ptr attrs begin end_ in
    forall e : entity_id,
      In e (owned_by new_abst a) <-> In e (owned_by abst a).
  Proof.
    cbv [abstract_reassign_pointer]; basics.
    apply fold_right_invariant_strong; basics.
    { erewrite abstract_reassign_pointer_for_vm_noop by solver.
      solver. }
    { cbv [abstract_reassign_pointer_for_entity].
      apply fold_right_invariant; basics; solver. }
  Qed.

  Definition vm_page_table_unchanged deref1 deref2 v : Prop :=
    forall ptr,
      index_sequences_to_pointer deref1 ptr (vm_ptable v) Stage2 <> nil
      \/ index_sequences_to_pointer deref2 ptr (vm_ptable v) Stage2 <> nil ->
      deref1 ptr = deref2 ptr.

  Definition hafnium_page_table_unchanged deref1 deref2 : Prop :=
    forall ptr,
      index_sequences_to_pointer deref1 ptr hafnium_ptable Stage1 <> nil
      \/ index_sequences_to_pointer deref2 ptr hafnium_ptable Stage1 <> nil ->
      deref1 ptr = deref2 ptr.

  Lemma vm_table_unchanged_sym deref1 deref2 v :
    vm_page_table_unchanged deref1 deref2 v ->
    vm_page_table_unchanged deref2 deref1 v.
  Proof.
    cbv [vm_page_table_unchanged]; basics;
      symmetry; solver.
  Qed.

  Lemma hafnium_table_unchanged_sym deref1 deref2 :
    hafnium_page_table_unchanged deref1 deref2 ->
    hafnium_page_table_unchanged deref2 deref1.
  Proof.
    cbv [hafnium_page_table_unchanged]; basics;
      symmetry; solver.
  Qed.

  (* Modifying the stage-1 table doesn't change the VM page tables *)
  Lemma vm_table_unchanged_stage1 deref ptr idxs t ppool :
    has_location deref ptr (table_loc ppool hafnium_ptable idxs) ->
    locations_exclusive deref ppool ->
    locations_exclusive (update_deref deref ptr t) ppool ->
    forall v,
      In v vms ->
      vm_page_table_unchanged deref (update_deref deref ptr t) v.
  Proof.
    cbv [vm_page_table_unchanged update_deref]; inversion 1; basics;
      break_match; basics; try solver;
        match goal with
        | H : _ <> nil |- _ =>
          apply index_sequences_has_location_stage2 with (ppool:=ppool) in H;
            [ basics | solver .. ]
        end;
        match goal with
        | H : context [has_location deref] |- _ =>
          pose proof H;
            apply has_location_update_deref with (t:=t) in H
        end;
        two_locations_contradiction;
        match goal with
        | H : _ |- _ => apply hafnium_neq_vm_ptable in H; solver
        | H : _ |- _ =>
          apply eq_sym in H; apply hafnium_neq_vm_ptable in H; solver
        end.
  Qed.

  (* Modifying the stage-2 tables doesn't change hafnium's table *)
  Lemma hafnium_table_unchanged_stage2 deref ptr idxs t ppool root_ptable :
    has_location deref ptr (table_loc ppool root_ptable idxs) ->
    In root_ptable (map vm_ptable vms) ->
    locations_exclusive deref ppool ->
    locations_exclusive (update_deref deref ptr t) ppool ->
    hafnium_page_table_unchanged deref (update_deref deref ptr t).
  Proof.
    pose proof hafnium_ptable_nodup.
    cbv [hafnium_page_table_unchanged update_deref]; inversion 1; basics;
      break_match; basics; try solver;
        match goal with
        | H : _ <> nil |- _ =>
          apply index_sequences_has_location_stage1 with (ppool:=ppool) in H;
            [ basics | solver .. ]
        end;
        match goal with
        | H : context [has_location deref] |- _ =>
          pose proof H;
            apply has_location_update_deref with (t:=t) in H
        end;
        two_locations_contradiction; try solver.
  Qed.

  (* if the changed pointer is in a different VM's page table, then other VMs' page tables are unchanged *)
  Lemma vm_table_unchanged_stage2 v1 v2 deref ptr t ppool idxs :
    has_location deref ptr (table_loc ppool (vm_ptable v1) idxs) ->
    locations_exclusive deref ppool ->
    locations_exclusive (update_deref deref ptr t) ppool ->
    In v1 vms ->
    In v2 vms ->
    v1 <> v2 ->
    vm_page_table_unchanged deref (update_deref deref ptr t) v2.
  Proof.
    cbv [vm_page_table_unchanged update_deref]; inversion 1; basics;
      break_match; basics; try solver;
        match goal with
        | H : _ <> nil |- _ =>
          apply index_sequences_has_location_stage2 with (ppool:=ppool) in H;
            [ basics | solver .. ]
        end;
        match goal with
        | H : context [has_location deref] |- _ =>
          pose proof H;
            apply has_location_update_deref with (t:=t) in H
        end;
        two_locations_contradiction;
        match goal with
        | H : _ |- _ => apply vm_ptable_nodup in H; solver
        end.
  Qed.

  (* If hafnium's table is unchanged, then haf_page_valid is the same for all
     addresses *)
  Lemma haf_page_valid_proper conc conc' a:
    hafnium_page_table_unchanged conc.(ptable_deref) conc'.(ptable_deref) ->
    haf_page_valid conc a ->
    haf_page_valid conc' a.
  Proof.
    cbv [haf_page_valid hafnium_page_table_unchanged page_attrs].
    basics.
    erewrite page_lookup_proper; [ eassumption | basics .. ];
      cbn [root_ptable_matches_stage]; try solver; [ ].
    match goal with H : _ |- _ => rewrite H; solver end.
  Qed.

  (* If hafnium's table is unchanged, then haf_page_owned is the same for all
     addresses *)
  Lemma haf_page_owned_proper conc conc' a:
    hafnium_page_table_unchanged conc.(ptable_deref) conc'.(ptable_deref) ->
    haf_page_owned conc a ->
    haf_page_owned conc' a.
  Proof. cbv [haf_page_owned]; eauto using haf_page_valid_proper. Qed.

  Lemma stage2_mode_has_value_proper conc conc' v a flag flag_value :
    vm_page_table_unchanged conc.(ptable_deref) conc'.(ptable_deref) v ->
    In v vms ->
    stage2_mode_has_value conc v a flag flag_value->
    stage2_mode_has_value conc' v a flag flag_value.
  Proof.
    cbv [stage2_mode_has_value vm_page_table_unchanged page_attrs].
    basics.
    pose_in_vm_ptable_map.
    erewrite page_lookup_proper; [ solver | basics .. ].
    match goal with H : _ |- _ => rewrite H; solver end.
  Qed.

  (* If a VM's page tables are unchanged, then vm_page_valid is the same for all
     addresses *)
  Lemma vm_page_valid_proper conc conc' v a:
    vm_page_table_unchanged conc.(ptable_deref) conc'.(ptable_deref) v ->
    In v vms ->
    vm_page_valid conc v a ->
    vm_page_valid conc' v a.
  Proof.
    cbv [vm_page_valid]; eauto using stage2_mode_has_value_proper.
  Qed.

  (* If a VM's page tables are unchanged, then vm_page_owned is the same for all
     addresses *)
  Lemma vm_page_owned_proper conc conc' v a:
    vm_page_table_unchanged conc.(ptable_deref) conc'.(ptable_deref) v  ->
    In v vms ->
    vm_page_owned conc v a ->
    vm_page_owned conc' v a.
  Proof.
    cbv [vm_page_owned]; eauto using stage2_mode_has_value_proper.
  Qed.

  (* TODO: move *)
  Lemma page_lookup_update_deref deref root_ptable idxs ppool stage a ptr t :
    root_ptable_matches_stage root_ptable stage ->
    has_location deref ptr (table_loc ppool root_ptable idxs) ->
    page_lookup (update_deref deref ptr t) root_ptable stage a
    = if address_matches_indices_dec stage a idxs
      then page_lookup' deref a t (level_from_indices stage idxs) stage
      else page_lookup deref root_ptable stage a.
  Admitted.


  (* TODO : move *)
  Lemma address_matches_indices_bool_iff a idxs stage :
    length idxs <= S (max_level stage) ->
    address_matches_indices_bool a idxs stage = true <-> address_matches_indices stage a idxs.
  Proof.
    cbv [address_matches_indices_bool indices_from_address address_matches_indices].
    repeat match goal with
           | _ => progress basics
           | H : _ = true |- _ => rewrite forallb_forall in H
           | |- _ = true => apply forallb_forall
           | |- _ = true => apply Nat.eqb_eq
           | H : In _ (seq _ _) |- _ => apply in_seq in H
           | H : context [Nat.eqb _ _ = true] |- @eq nat _ _ =>
             erewrite nth_indep by solver;
               apply Nat.eqb_eq; apply H; apply in_seq
           | |- _ <-> _ => split
           | _ => solver
           | H : _ |- _ => apply H; solver
           end.
  Qed.

  (* TODO : move *)
  Lemma addresses_under_pointer_in_range_iff
        deref ppool ptr root_ptable begin end_ stage a idxs :
    has_location deref ptr (table_loc ppool root_ptable idxs) ->
    locations_exclusive deref ppool ->
    root_ptable_matches_stage root_ptable stage ->
    In a (addresses_under_pointer_in_range deref ptr root_ptable begin end_ stage)
    <-> (address_matches_indices stage (pa_addr a) idxs /\ (begin <= va_addr (va_from_pa a) < end_)%N).
  Proof.
    cbv [addresses_under_pointer_in_range]; basics.
    match goal with H : _ |- _ =>
                    pose proof H;
                      eapply has_location_index_sequences_not_nil in H; [ | solver .. ]
    end.
    match goal with H : context [has_location] |- _ =>
                    pose proof H;
                      eapply has_location_length in H; [ | solver .. ]
    end.
    break_match; [ solver | ].
    match goal with H : ?ls = ?x :: _ |- _ =>
                    replace x with (hd nil ls) by (rewrite H; solver)
    end.
    erewrite has_location_hd_index_sequences by solver.
    rewrite filter_In.
    repeat match goal with
           | _ => progress basics
           | _ => progress rewrite ?pa_from_va_id, ?va_from_pa_id, ?va_addr_id, ?va_init_id
           | |- exists x : uintvaddr_t, pa_from_va (va_init x) = ?a /\ _ =>
             exists (va_addr (va_from_pa a))
           | |- exists x : nat, N.of_nat x = ?y /\ _ =>
             exists (N.to_nat y)
           | H : In _ (seq _ _) |- _ => apply in_seq in H
           | |- In _ (seq _ _) => apply in_seq
           | H : In _ (map _ _) |- _ => apply in_map_iff in H
           | |- In _ (map _ _) => apply in_map_iff
           | H : _ = true |- _ => apply address_matches_indices_bool_iff in H;
                                    [ | solver .. ]
           | |- _ = true => apply address_matches_indices_bool_iff; [ | solver .. ]
           | |- _ <-> _ => split
           | _ => solver
           end.
  Qed.

  (* TODO : move *)
  Lemma page_attrs_outside_range
        deref ppool root_ptable stage idxs ptr t level begin end_ a :
    root_ptable_matches_stage root_ptable stage ->
    has_location deref ptr (table_loc ppool root_ptable idxs) ->
    locations_exclusive deref ppool ->
    attrs_outside_range_unchanged deref idxs (deref ptr) t level begin end_ stage ->
    ~ In a (addresses_under_pointer_in_range deref ptr root_ptable begin end_ stage) ->
    level = level_from_indices stage idxs ->
    page_attrs (update_deref deref ptr t) root_ptable stage (pa_addr a)
    = page_attrs deref root_ptable stage (pa_addr a).
  Proof.
    basics. cbv [page_attrs]; erewrite page_lookup_update_deref by eauto.
    break_match; [ | solver ].
    cbv [attrs_outside_range_unchanged page_attrs'] in *.
    erewrite page_table_lookup_equiv by eauto using has_location_table_lookup.
    rewrite <-(pa_from_va_id a), <-(va_init_id (va_from_pa a)).
    match goal with H : forall a_v : uintvaddr_t, _ |- _ => rewrite H end;
      rewrite ?va_init_id, ?pa_from_va_id; try solver; [ ].
    match goal with H : _ |- _ =>
                    rewrite addresses_under_pointer_in_range_iff in H by solver;
                      apply Decidable.not_and in H;
                      [ | apply address_matches_indices_decidable ]
    end.
    basics; solver.
  Qed.

  (* If an address isn't in the range that changed, then stage2_mode_has_value
     is unchanged. *)
  Lemma stage2_mode_has_value_unaffected_address
        flag flag_value conc ptr ppool v a begin end_ attrs idxs level t :
    (* ptr exists in v's page table *)
    has_location
      (ptable_deref conc) ptr (table_loc ppool (vm_ptable v) idxs) ->
    (* locations_exclusive holds *)
    locations_exclusive (ptable_deref conc) ppool ->
    (* attributes of the new table match the old, except in the range specified *)
    attrs_changed_in_range (ptable_deref conc) idxs (ptable_deref conc ptr) t
                           level attrs begin end_ Stage2 ->
    (* a is not one of the addresses that changed *)
    ~ In a (addresses_under_pointer_in_range
              conc.(ptable_deref) ptr (vm_ptable v) begin end_ Stage2) ->
    In v vms ->
    level = level_from_indices Stage2 idxs ->
    stage2_mode_has_value conc v a flag flag_value
    <-> stage2_mode_has_value (reassign_pointer conc ptr t) v a flag flag_value.
  Proof.
    cbv [attrs_changed_in_range stage2_mode_has_value];
      cbn [reassign_pointer ptable_deref]; basics.
    pose_in_vm_ptable_map.
    erewrite page_attrs_outside_range by (cbn [root_ptable_matches_stage]; solver).
    solver.
  Qed.

  (* If an address isn't in the range that changed, then vm_page_valid remains
     true (specialized version of stage2_mode_has_value_unaffected_address) *)
  Lemma vm_page_valid_unaffected_address
        conc ptr ppool v a begin end_ attrs idxs level t :
    has_location
      (ptable_deref conc) ptr (table_loc ppool (vm_ptable v) idxs) ->
    locations_exclusive (ptable_deref conc) ppool ->
    attrs_changed_in_range (ptable_deref conc) idxs (ptable_deref conc ptr) t
                           level attrs begin end_ Stage2 ->
    ~ In a (addresses_under_pointer_in_range
              conc.(ptable_deref) ptr (vm_ptable v) begin end_ Stage2) ->
    In v vms ->
    level = level_from_indices Stage2 idxs ->
    vm_page_valid conc v a <-> vm_page_valid (reassign_pointer conc ptr t) v a.
  Proof.
    cbv [vm_page_valid]; eauto using stage2_mode_has_value_unaffected_address.
  Qed.

  (* If an address isn't in the range that changed, then vm_page_owned remains
     true (specialized version of stage2_mode_has_value_unaffected_address) *)
  Lemma vm_page_owned_unaffected_address
        conc ptr ppool v a begin end_ attrs idxs level t :
    has_location
      (ptable_deref conc) ptr (table_loc ppool (vm_ptable v) idxs) ->
    locations_exclusive (ptable_deref conc) ppool ->
    attrs_changed_in_range (ptable_deref conc) idxs (ptable_deref conc ptr) t
                           level attrs begin end_ Stage2 ->
    ~ In a (addresses_under_pointer_in_range
              conc.(ptable_deref) ptr (vm_ptable v) begin end_ Stage2) ->
    In v vms ->
    level = level_from_indices Stage2 idxs ->
    vm_page_owned conc v a <-> vm_page_owned (reassign_pointer conc ptr t) v a.
  Proof.
    cbv [vm_page_owned]; eauto using stage2_mode_has_value_unaffected_address.
  Qed.

  (* If an address isn't in the range that changed, then haf_page_valid remains true *)
  Lemma haf_page_valid_unaffected_address
        conc ptr ppool a begin end_ attrs idxs level t :
    (* ptr exists in v's page table *)
    has_location
      (ptable_deref conc) ptr (table_loc ppool hafnium_ptable idxs) ->
    locations_exclusive (ptable_deref conc) ppool ->
    (* attributes of the new table match the old, except in the range specified *)
    attrs_changed_in_range (ptable_deref conc) idxs (ptable_deref conc ptr) t
                           level attrs begin end_ Stage1 ->
    (* a is not one of the addresses that changed *)
    ~ In a (addresses_under_pointer_in_range
              conc.(ptable_deref) ptr hafnium_ptable begin end_ Stage1) ->
    level = level_from_indices Stage1 idxs ->
    haf_page_valid conc a <-> haf_page_valid (reassign_pointer conc ptr t) a.
  Proof.
    cbv [attrs_changed_in_range haf_page_valid];
      cbn [reassign_pointer ptable_deref]; basics.
    erewrite page_attrs_outside_range by (cbn [root_ptable_matches_stage]; solver).
    solver.
  Qed.

  (* If an address isn't in the range that changed, then haf_page_owned remains true *)
  Lemma haf_page_owned_unaffected_address
        conc ptr ppool a begin end_ attrs idxs level t :
    (* ptr exists in v's page table *)
    has_location
      (ptable_deref conc) ptr (table_loc ppool hafnium_ptable idxs) ->
    (* attributes of the new table match the old, except in the range specified *)
    attrs_changed_in_range (ptable_deref conc) idxs (ptable_deref conc ptr) t
                           level attrs begin end_ Stage1 ->
    (* a is not one of the addresses that changed *)
    ~ In a (addresses_under_pointer_in_range
              conc.(ptable_deref) ptr hafnium_ptable begin end_ Stage1) ->
    haf_page_owned conc a <-> haf_page_owned (reassign_pointer conc ptr t) a.
  Proof. cbv [haf_page_owned]; basics; solver. Qed.

  Lemma changed_has_new_attrs
        deref ppool ptr t a level attrs begin end_ idxs root_ptable stage:
    has_location deref ptr (table_loc ppool root_ptable idxs) ->
    locations_exclusive deref ppool ->
    address_wf (pa_addr a) stage ->
    root_ptable_wf (update_deref deref ptr t) stage root_ptable ->
    level = level_from_indices stage idxs ->
    root_ptable_matches_stage root_ptable stage ->
    attrs_changed_in_range
      deref idxs (deref ptr) t level attrs begin end_ stage ->
    In a (addresses_under_pointer_in_range
            deref ptr root_ptable begin end_ stage) ->
    attrs_equiv
      (page_attrs
         (update_deref deref ptr t) root_ptable stage (pa_addr a))
      attrs.
  Proof.
    cbv [attrs_changed_in_range]; basics.
    cbv [has_uniform_attrs page_attrs page_attrs'] in *.
    erewrite page_lookup_update_deref by solver.
    rewrite addresses_under_pointer_in_range_iff in * by solver.
    basics; break_match; [ | solver ].
    rewrite <-(pa_from_va_id a).
    rewrite <-(va_init_id (va_from_pa a)).
    match goal with H : _ |- _ => apply H end;
      rewrite ?va_init_id, ?pa_from_va_id; solver.
  Qed.

  Lemma attrs_equiv_valid attrs1 attrs2 :
    attrs_equiv attrs1 attrs2 ->
    ((attrs1 & PTE_VALID) =? 0)%N = ((attrs2 & PTE_VALID) =? 0)%N.
  Proof.
    cbv [attrs_equiv attrs_present];
      repeat match goal with
             | _ => progress basics
             | _ => inversion_bool
             | _ => solver
             end.
  Qed.

  Lemma attrs_equiv_to_mode attrs1 attrs2 flag :
    (flag = MM_MODE_UNOWNED \/ flag = MM_MODE_INVALID) ->
    attrs_equiv attrs1 attrs2 ->
    ((arch_mm_stage2_attrs_to_mode attrs1 & flag) =? 0)%N
    = ((arch_mm_stage2_attrs_to_mode attrs2 & flag) =? 0)%N.
  Proof.
    cbv [attrs_equiv attrs_present];
      repeat match goal with
             | _ => progress basics
             | H : ( _ =? _)%N = _ |- _ => rewrite H
             | H : _ |- _ => rewrite stage2_attrs_to_mode_valid in H
             | _ => inversion_bool
             | _ => solver
             end.
  Qed.

  Lemma changed_has_new_attrs_stage2
        conc ppool ptr v t a level attrs begin end_ idxs :
    let deref := conc.(ptable_deref) in
    has_location deref ptr (table_loc ppool (vm_ptable v) idxs) ->
    locations_exclusive deref ppool ->
    address_wf (pa_addr a) Stage2 ->
    root_ptable_wf (update_deref deref ptr t) Stage2 (vm_ptable v) ->
    level = level_from_indices Stage2 idxs ->
    In (vm_ptable v) (map vm_ptable vms) ->
    attrs_changed_in_range
      deref idxs (deref ptr) t level attrs begin end_ Stage2 ->
    In a (addresses_under_pointer_in_range
            deref ptr (vm_ptable v) begin end_ Stage2) ->
    forall flag value,
      (flag = MM_MODE_UNOWNED \/ flag = MM_MODE_INVALID) ->
      stage2_mode_flag_set attrs flag = value ->
      stage2_mode_has_value (reassign_pointer conc ptr t) v a flag value.
  Proof.
    cbv [stage2_mode_flag_set stage2_mode_has_value];
      cbn [reassign_pointer ptable_deref]; basics;
        erewrite attrs_equiv_to_mode
        by eauto using changed_has_new_attrs; solver.
  Qed.

  Local Ltac solve_table_unchanged_step :=
    first [ eapply vm_table_unchanged_stage2; solver
          | eapply vm_table_unchanged_stage1; solver
          | eapply hafnium_table_unchanged_stage2; solver ].

  Local Ltac solve_table_unchanged :=
    first [ solve_table_unchanged_step
          | apply vm_table_unchanged_sym;
            solve_table_unchanged_step
          | apply hafnium_table_unchanged_sym;
            solve_table_unchanged_step ].

  Local Ltac solve_unaffected_address conc :=
    first [ eapply vm_page_valid_unaffected_address with (conc:=conc)
          | eapply vm_page_owned_unaffected_address with (conc:=conc)
          | eapply haf_page_valid_unaffected_address with (conc:=conc)
          | eapply haf_page_owned_unaffected_address with (conc:=conc) ];
    solver.

  (* simplify [reassign_pointer_represents] subgoals *)
  Local Ltac process_represents :=
      repeat match goal with
             | _ => progress basics
             | |- _ <-> _ => split
             | |- inl _ = inr _ \/ _ => right
             | |- inr _ = inl _ \/ _ => right
             | H : context [(In (inr hid) _ <-> ?f _ _)],
                   H' : In (inr hid) _ |- ?f _ _ => apply H in H'
             | H : context [In (inr hid) _ <-> ?f _ _]
               |- In (inr hid) _ => apply H
             | H : context [In (inl _) _ <-> exists _, _],
                   H' : In (inl _) _ |- exists _, _ =>
               apply H in H'; try (let x := fresh in destruct H' as [x H']; exists x)
             | H : context [In (inl _) _ <-> exists _, _]
               |- context [In (inl _) _] => rewrite H
             | _ => destruct_vm_eq
             | H : vm_find _ = Some _ |- _ =>
               rewrite (vm_find_sound _ _ H) in * by auto
             | H : vm_find ?vid = Some ?x, H' : ?v <> ?x
               |- inl ?vid = inl (vm_id ?v) \/ _ => right
             | H : ~ In _ (addresses_under_pointer_in_range
                             (ptable_deref ?conc) _ _ _ _ _) |- _ =>
               solve_unaffected_address conc
             | _ => break_match
             | |- exists _, _ /\ _ => eexists; split; eauto using vm_find_Some; [ ]
             | |- exists _, _ /\ _ => eexists; split; try eassumption; [ ]
             | _ => solver
             | _ => eapply vm_page_valid_proper; [|solver .. ];
                    solve_table_unchanged
             | _ => eapply vm_page_owned_proper; [|solver .. ];
                    solve_table_unchanged
             | _ => eapply haf_page_valid_proper; [|solver .. ];
                    solve_table_unchanged
             | _ => eapply haf_page_owned_proper; [|solver ..];
                    solve_table_unchanged
             end.

  Lemma reassign_pointer_represents_stage1 conc ptr t abst idxs :
    represents abst conc ->
    has_location (ptable_deref conc) ptr
                 (table_loc (api_page_pool conc) hafnium_ptable idxs) ->
    let conc' := conc.(reassign_pointer) ptr t in
    let level := level_from_indices Stage1 idxs in
    is_valid conc ->
    is_valid conc' ->
    forall attrs begin end_,
      attrs_changed_in_range (ptable_deref conc) idxs (ptable_deref conc ptr) t
                             level attrs begin end_ Stage1 ->
      represents (abstract_reassign_pointer
                    abst conc ptr attrs begin end_)
                 conc'.
  Proof.
    cbv [represents is_valid].
    cbv [has_location_in_state].
    cbn [reassign_pointer ptable_deref api_page_pool].
    basics; try solver; [ | | | ].
    { (* stage-2 [accessible_by] states match *)
      rewrite accessible_by_abstract_reassign_pointer_stage1 by eauto.
      process_represents. }
    { (* stage-1 [accessible_by] states match *)
      rewrite accessible_by_abstract_reassign_pointer_stage1 by eauto.
      process_represents;
        cbv [haf_page_valid] in *; basics; cbn [ptable_deref] in *;
          try match goal with
              | H : root_ptable_wf ?deref _ _
                |- context [page_lookup ?deref ?t ?s ?a] =>
                pose proof H; eapply page_lookup_ok in H; eauto; [ ];
                  case_eq (page_lookup deref t s a); basics; try solver; [ ]
              end;
          repeat match goal with
                 | _ => progress basics
                 | _ => progress destruct_tuples
                 | _ => progress cbn [ptable_deref reassign_pointer] in *
                 | H : stage1_valid _ = _ |- _ =>
                   cbv [stage1_valid] in H;
                     erewrite <-attrs_equiv_valid in H
                     by (eapply changed_has_new_attrs; solver)
                 | _ => solver
                 | _ => repeat inversion_bool; solver
                 end. }
    { (* stage-2 [owned_by] states match *)
      rewrite owned_by_abstract_reassign_pointer_stage1 by eauto.
      process_represents. }
    { (* stage-1 [owned_by] states match *)
      rewrite owned_by_abstract_reassign_pointer_stage1 by eauto.
      process_represents. }
  Qed.

  Local Ltac solve_by_stage2_mode :=
    repeat match goal with
           | H : stage2_mode_flag_set _ _ = _ |- _ =>
             eapply changed_has_new_attrs_stage2 in H; [ try solver | solver ..]
           | _ : ?P true, _ : ?P false |- _ =>
             cbv [stage2_mode_has_value] in *; basics; solver
           end.

  Lemma reassign_pointer_represents_stage2 conc ptr t abst idxs v :
    represents abst conc ->
    In v vms ->
    has_location (ptable_deref conc) ptr
                 (table_loc (api_page_pool conc) (vm_ptable v) idxs) ->
    let conc' := conc.(reassign_pointer) ptr t in
    is_valid conc ->
    is_valid conc' ->
    forall attrs level begin end_,
      attrs_changed_in_range (ptable_deref conc) idxs (ptable_deref conc ptr) t
                             level attrs begin end_ Stage2 ->
      level = level_from_indices Stage2 idxs ->
      represents (abstract_reassign_pointer
                    abst conc ptr attrs begin end_)
                 conc'.
  Proof.
    cbv [represents is_valid].
    cbv [has_location_in_state].
    cbn [reassign_pointer ptable_deref] in *.
    intros. assert (In (vm_ptable v) (map vm_ptable vms)) by (apply in_map_iff; eauto).
    rewrite Forall_forall in *.
    basics; try solver; [ | | | ].
    { (* stage-2 [accessible_by] states match *)
        rewrite accessible_by_abstract_reassign_pointer_stage2 by eauto.
        process_represents; cbv [vm_page_valid] in *; solve_by_stage2_mode. }
    { (* stage-1 [accessible_by] states match *)
      rewrite accessible_by_abstract_reassign_pointer_stage2 by eauto.
      process_represents. }
    { (* stage-2 [owned_by] states match *)
      rewrite owned_by_abstract_reassign_pointer_stage2 by eauto.
        process_represents; cbv [vm_page_owned] in *; solve_by_stage2_mode. }
    { (* stage-1 [owned_by] states match *)
      rewrite owned_by_abstract_reassign_pointer_stage2 by eauto.
      process_represents. }
  Qed.

  Lemma reassign_pointer_represents conc ptr t abst idxs root_ptable stage :
    represents abst conc ->
    has_location (ptable_deref conc) ptr
                 (table_loc (api_page_pool conc) root_ptable idxs) ->
    root_ptable_matches_stage root_ptable stage ->
    let conc' := conc.(reassign_pointer) ptr t in
    is_valid conc ->
    is_valid conc' ->
    forall attrs level begin end_,
      attrs_changed_in_range (ptable_deref conc) idxs (ptable_deref conc ptr) t
                             level attrs begin end_ stage ->
      level = level_from_indices stage idxs ->
      represents (abstract_reassign_pointer
                    abst conc ptr attrs begin end_)
                 conc'.
  Proof.
    cbv [has_location_in_state root_ptable_matches_stage].
    intros.
    assert (~ In hafnium_ptable (map vm_ptable vms))
      by (pose proof no_duplicate_ptables; cbv [all_root_ptables] in *;
          invert_list_properties; solver).
    match goal with
    | H : context [has_location _] |- _ => pose proof H; invert H
    end; (destruct stage; try solver; [ ]).
    { eapply reassign_pointer_represents_stage1; eauto. }
    { match goal with
      | H : _ |- _ => apply in_map_iff in H; basics
      end.
      eapply reassign_pointer_represents_stage2; eauto. }
  Qed.

  (* if the address range is empty (end_ <= begin), then there can be no
     addresses in that range under the given pointer *)
  Lemma addresses_under_pointer_in_range_empty
        deref ptr root_ptbl begin end_ stage :
    (end_ <= begin)%N ->
    addresses_under_pointer_in_range deref ptr root_ptbl begin end_ stage = nil.
  Proof.
    intros; cbv [addresses_under_pointer_in_range].
    replace (end_ - begin)%N with 0%N by solver.
    break_match; reflexivity.
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

  (* attrs_changed_in_range doesn't care if we reassign the pointer we started from *)
  (* TODO : fill in preconditions *)
  (* TODO : currently unused; remove if not used in mm_map_level proofs *)
  Lemma attrs_changed_in_range_reassign_pointer
        c ptr new_table t level attrs begin end_ idxs stage :
    (* this precondition is so we know c doesn't show up in the new table *)
    is_valid (reassign_pointer c ptr new_table) ->
    has_location_in_state c ptr idxs ->
    attrs_changed_in_range
      (ptable_deref c) idxs (ptable_deref c ptr) t level attrs begin end_ stage ->
    attrs_changed_in_range
      (ptable_deref (reassign_pointer c ptr new_table))
      idxs (ptable_deref c ptr) t level attrs begin end_ stage.
  Admitted. (* TODO *)

  Definition no_addresses_in_range deref ptr begin end_ : Prop :=
    Forall
      (fun root_ptable =>
         addresses_under_pointer_in_range deref ptr root_ptable begin end_ Stage2 = nil)
      (map vm_ptable vms)
    /\ addresses_under_pointer_in_range deref ptr hafnium_ptable begin end_ Stage1 = nil.

  Lemma locations_exclusive_update_deref
        deref ppool ppool' ptr t :
    has_location deref ptr (mpool_loc ppool) ->
    locations_exclusive deref ppool ->
    mpool_alloc ppool = Some (ppool', ptr) ->
    forall level,
      Forall (fun pte =>
                arch_mm_pte_is_table pte level = false) (entries t) ->
    locations_exclusive (update_deref deref ptr t) ppool'.
  Proof.
    cbv [locations_exclusive]; basics.
    invert H.
    (* actually, there are no new pointers added here... *)
    (* TODO *)
  Admitted.

  (* reassign_pointer is a no-op if there are no addresses in range *)
  Lemma reassign_pointer_no_addresses
        abst ppool ppool' conc ptr t:
    has_location conc.(ptable_deref) ptr (mpool_loc ppool) ->
    locations_exclusive conc.(ptable_deref) ppool ->
    mpool_alloc ppool = Some (ppool', ptr) ->
    represents abst conc ->
    represents abst (reassign_pointer (update_page_pool conc ppool') ptr t).
  Proof.
    cbv [represents is_valid reassign_pointer update_page_pool].
    cbn [ptable_deref api_page_pool].
    basics; process_represents; rewrite Forall_forall in *.
  Admitted. (* TODO *)

  (* if fallback unused, then ptr must have been in local ppool and therefore disjoint from tables *)
  Lemma reassign_pointer_no_addresses_fallback_unused
        abst ppool ppool' conc ptr t:
    has_location conc.(ptable_deref) ptr (mpool_loc ppool) ->
    locations_exclusive conc.(ptable_deref) ppool ->
    mpool_alloc ppool = Some (ppool', ptr) ->
    mpool_fallback ppool = Some (api_page_pool conc) ->
    mpool_fallback ppool' = Some (api_page_pool conc) ->
    represents abst conc ->
    represents abst (reassign_pointer conc ptr t).
  Proof.
    cbv [represents is_valid reassign_pointer update_page_pool].
    cbn [ptable_deref api_page_pool].
    basics; process_represents; rewrite Forall_forall in *.
  Admitted. (* TODO *)

  (* abstract_reassign_pointer is a no-op if the given tables don't have any
     addresses in range *)
  Lemma abstract_reassign_pointer_no_addresses
        abst conc attrs begin end_ t_ptr :
    no_addresses_in_range conc.(ptable_deref) t_ptr begin end_ ->
    abstract_state_equiv
      abst
      (abstract_reassign_pointer abst conc t_ptr attrs begin end_).
  Proof.
    cbv [no_addresses_in_range abstract_reassign_pointer].
    basics. rewrite Forall_forall in *.
    apply fold_right_invariant_strong; basics.
    { pose_in_vm_ptable_map.
      erewrite abstract_reassign_pointer_noop; solver. }
    { erewrite abstract_reassign_pointer_noop; solver. }
  Qed.

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
  Proof.
    rewrite Forall_forall; basics.
    apply fold_left_invariant_strong; [ basics | solver ].
    eapply abstract_state_equiv_trans; [ solver | ].
    auto using abstract_reassign_pointer_no_addresses.
  Qed.

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
  Proof.
    rewrite Forall_forall; basics.
    destruct (Compare_dec.le_dec i (length t_ptrs));
      [ | autorewrite with push_firstn; solver ].
    rewrite <-(firstn_skipn i t_ptrs).
    autorewrite with push_firstn.
    rewrite Nat.min_id, fold_left_app.
    apply fold_left_invariant_strong with (ls:=skipn _ _); [ basics | solver ].
    eapply abstract_state_equiv_trans; [ solver | ].
    auto using abstract_reassign_pointer_no_addresses.
  Qed.
End Proofs.
