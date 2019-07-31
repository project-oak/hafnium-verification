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
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.BinNat.
Require Import Coq.omega.Omega.
Require Import Hafnium.AbstractModel.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Notations.
Require Import Hafnium.Concrete.PointerLocations.
Require Import Hafnium.Concrete.State.
Require Import Hafnium.Concrete.StateProofs.
Require Import Hafnium.Util.BinNat.
Require Import Hafnium.Util.List.
Require Import Hafnium.Util.Loops.
Require Import Hafnium.Util.Tactics.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.ArchMM.
Require Import Hafnium.Concrete.Assumptions.Constants.
Require Import Hafnium.Concrete.Assumptions.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Mpool.
Require Import Hafnium.Concrete.Assumptions.PageTables.
Require Import Hafnium.Concrete.MM.Datatypes.
Require Import Hafnium.Concrete.MM.Implementation.

(*** This file contains correctness proofs for the functions in mm.c, as
     transcribed in MM/Implementation.v ***)

Section Proofs.
  Context {ap : @abstract_state_parameters paddr_t nat}
          {cp : concrete_params} {cp_ok : params_valid}.

  Local Definition preserves_represents_valid
        (f : concrete_state -> concrete_state) : Prop :=
    forall (conc : concrete_state),
      (exists abst, represents_valid abst conc) ->
      exists abst', represents_valid abst' (f conc).
  Hint Unfold preserves_represents_valid.

  Ltac simplify_step :=
    match goal with
    | _ => progress basics
    | _ => progress cbn [fst snd] in *
    | p : _ * _ |- _ => destruct p
    | |- context [let '(_,_) := ?x in _] =>
      rewrite (surjective_pairing x)
    | H : context [let '(_,_) := ?x in _] |- _ =>
      rewrite (surjective_pairing x) in H
    | _ => break_match
    | _ => solver
    | H : break = continue |- _ => cbv [break continue] in H; solver
    | H : continue = break |- _ => cbv [break continue] in H; solver
    end.
  Ltac simplify := repeat simplify_step.

  (*** shorthand definitions ***)

  Definition is_start_of_block (a : uintvaddr_t) (block_size : size_t) : Prop :=
    (a & (block_size - 1))%N = 0.

  Definition is_root (level : nat) (flags : int) : Prop :=
    level = mm_max_level flags + 1.

  Definition ptable_is_root (t : mm_ptable) (flags : int) : Prop :=
    if ((flags & MM_FLAG_STAGE1) != 0)%N
    then t = hafnium_ptable
    else In t (map vm_ptable vms).

  Definition stage_from_flags (flags : int) : Stage :=
    if ((flags & MM_FLAG_STAGE1) != 0)%N
    then Stage1
    else Stage2.

  Notation uintvaddr_to_uintpaddr a := (pa_addr (pa_from_va (va_init a))) (only parsing).

  (*** Generally useful lemmas ***)

  Lemma root_pos level flags : is_root level flags -> 0 < level.
  Proof. cbv [is_root]; simplify. Qed.

  Lemma root_le_max_level level flags :
    is_root level flags -> level <= max_level (stage_from_flags flags) + 1.
  Proof. cbv [is_root mm_max_level max_level stage_from_flags]; simplify. Qed.

  Lemma ptable_is_root_In (t : mm_ptable) (flags : int) :
    ptable_is_root t flags ->
    In t all_root_ptables.
  Proof.
    cbv [all_root_ptables ptable_is_root]; intros.
    break_match; subst; auto using in_eq, in_cons.
  Qed.

  (* if [begin] is the start of the block at the level above, then we can freely
     use a smaller address for [begin], because [has_uniform_attrs] ignores
     addresses outside of [table]'s range. *)
  Lemma has_uniform_attrs_block_start
        ptable_deref table level attrs begin end_ idxs stage :
    is_start_of_block begin (mm_entry_size level) ->
    address_matches_indices (uintvaddr_to_uintpaddr begin) idxs stage ->
    forall begin',
      (begin' <= begin)%N ->
      has_uniform_attrs ptable_deref idxs table (level - 1) attrs begin end_ stage ->
      has_uniform_attrs ptable_deref idxs table (level - 1) attrs begin' end_ stage.
  Admitted.

  (*** Proofs about [mm_page_table_from_pa] ***)

  Lemma mm_page_table_from_pa_length t flags :
    ptable_is_root t flags ->
    length (mm_page_table_from_pa t.(root)) = mm_root_table_count flags.
  Proof.
    cbv [mm_root_table_count ptable_is_root mm_page_table_from_pa]; intros.
    break_match; simplify;
      eauto using correct_number_of_root_tables_stage1,
      correct_number_of_root_tables_stage2.
  Qed.

  Lemma has_location_in_state_root root_level flags c t i :
    is_root root_level flags ->
    ptable_is_root t flags ->
    i < length (mm_page_table_from_pa (root t)) ->
    has_location_in_state c (nth_default_oobe (mm_page_table_from_pa (root t)) i) (cons i nil).
  Admitted. (* TODO *)
  Hint Resolve has_location_in_state_root.

  (*** Proofs about [mm_max_level] ***)

  Lemma mm_max_level_eq flags :
    mm_max_level flags = max_level (stage_from_flags flags).
  Proof. cbv [mm_max_level max_level stage_from_flags]; simplify. Qed.

  (*** Proofs about [mm_root_table_count] ***)

  Lemma mm_root_table_count_upper_bound flags :
    mm_root_table_count flags < 2 ^ PAGE_LEVEL_BITS.
  Proof.
    cbv [mm_root_table_count]; break_match;
      auto using stage1_root_table_count_ok, stage2_root_table_count_ok.
  Qed.

  (*** Proofs about [mm_entry_size] ***)

  Lemma mm_entry_size_eq level :
    mm_entry_size level = 2 ^ (PAGE_BITS + level * PAGE_LEVEL_BITS).
  Proof.
    cbv [mm_entry_size].
    apply Nnat.Nat2N.inj_iff.
    autorewrite with bits2arith push_nat2n nsimplify.
    solver.
  Qed.

  Lemma mm_entry_size_power_two level :
    N.is_power_of_two (N.of_nat (mm_entry_size level)).
  Proof. cbv [mm_entry_size]; push_nat2n; auto. Qed.

  Lemma mm_entry_size_gt_1 level : (1 < mm_entry_size level)%N.
  Proof.
    intros; rewrite mm_entry_size_eq.
    pose proof PAGE_BITS_pos.
    push_nat2n.
    change 1%N with (2 ^ 0)%N.
    apply N.pow_lt_mono_r; solver.
  Qed.

  Lemma mm_entry_size_pos level : (0 < mm_entry_size level)%N.
  Proof. pose proof mm_entry_size_gt_1 level; solver. Qed.

  Lemma mm_entry_size_step level :
    mm_entry_size (level + 1) = mm_entry_size level * 2 ^ PAGE_LEVEL_BITS.
  Proof.
    rewrite !mm_entry_size_eq.
    replace (PAGE_BITS + (level + 1) * PAGE_LEVEL_BITS)
      with (PAGE_BITS + level * PAGE_LEVEL_BITS + PAGE_LEVEL_BITS) by solver.
    apply Nat.pow_add_r.
  Qed.

  (*** Proofs about [mm_start_of_next_block] ***)

  Lemma mm_start_of_next_block_eq a block_size :
    N.is_power_of_two (N.of_nat block_size) ->
    mm_start_of_next_block a block_size = (a + block_size - a mod block_size)%N.
  Proof.
    cbv [mm_start_of_next_block]; intros.
    rewrite N.and_not, N.mod_add_cancel_r by auto.
    reflexivity.
  Qed.

  Lemma mm_start_of_next_block_eq' a block_size :
    N.is_power_of_two (N.of_nat block_size) ->
    @eq N (mm_start_of_next_block a block_size) ((a / block_size + 1) * block_size)%N.
  Proof.
    intros. rewrite mm_start_of_next_block_eq by auto.
    match goal with |- context [(?a + ?m - ?a mod ?m)%N] =>
                    replace (a + m - a mod m)%N with (m + (a - a mod m))%N
                      by (rewrite N.mod_eq; solver);
                      rewrite <-(N.mul_div a m) by solver
    end.
    solver.
  Qed.

  Lemma mm_start_of_next_block_is_start a block_size :
    N.is_power_of_two (N.of_nat block_size) ->
    is_start_of_block (mm_start_of_next_block a block_size) block_size.
  Proof.
    cbv [is_start_of_block]; intros.
    rewrite mm_start_of_next_block_eq' by auto.
    autorewrite with bits2arith nsimplify.
    reflexivity.
  Qed.

  Lemma mm_start_of_next_block_div a block_size :
    N.is_power_of_two (N.of_nat block_size) ->
    (mm_start_of_next_block a block_size / block_size =
    (a / N.of_nat block_size) + 1)%N.
  Proof.
    intros.
    rewrite <-(N.pow2_log2 (N.of_nat block_size)) by auto.
    cbv [mm_start_of_next_block].
    repeat match goal with
           | _ => progress simplify
           | _ => progress autorewrite with push_n2nat bits2arith nsimplify
           | _ => progress nsimplify_mod
           | |- context [(?a + ?m - ?a mod ?m)%N] =>
             replace (a + m - a mod m)%N with (m + (a - a mod m))%N
               by (rewrite N.mod_eq; solver);
               rewrite <-(N.mul_div a m) by solver
           end.
  Qed.

  Lemma mm_start_of_next_block_shift a level :
    (mm_start_of_next_block a (mm_entry_size level)
                            >> (PAGE_BITS + level * PAGE_LEVEL_BITS))%N =
    ((a >> (PAGE_BITS + level * PAGE_LEVEL_BITS)) + 1)%N.
  Proof.
    intros.
    rewrite mm_entry_size_eq.
    autorewrite with bits2arith pull_nat2n.
    apply mm_start_of_next_block_div; autorewrite with push_nat2n; auto.
  Qed.

  Lemma mm_index_start_of_next_block_previous a b level :
    (0 < b <= mm_entry_size level)%N ->
    mm_index (mm_start_of_next_block a (mm_entry_size level) - b) level = mm_index a level.
  Proof.
    cbv [mm_index mm_entry_size]; intros.
    apply Nnat.N2Nat.inj_iff.
    repeat match goal with
           | _ => progress autorewrite with push_n2nat bits2arith nsimplify in *
           | _ => rewrite mm_start_of_next_block_eq' by (push_n2nat; auto)
           | _ => rewrite N.div_sub_small by solver
           | _ => solver
           end.
  Qed.

  (* helper lemma for mm_index_start_of_next_block *)
  Lemma level_bits_small a level :
    (mm_start_of_next_block a (mm_entry_size level) < mm_level_end a level)%N ->
    ((a / 2 ^ (PAGE_BITS + level * PAGE_LEVEL_BITS)) mod 2 ^ PAGE_LEVEL_BITS + 1 < 2 ^ PAGE_LEVEL_BITS)%N.
  Proof.
    cbv [mm_level_end]; intros.
    let H := fresh in
    pose proof mm_start_of_next_block_div
         a (mm_entry_size level) ltac:(auto using mm_entry_size_power_two) as H;
      remember (mm_start_of_next_block a (mm_entry_size level));
      rewrite mm_entry_size_eq in H.
    autorewrite with push_nat2n push_nmul in *.
    repeat match goal with
           | _ => progress autorewrite with bits2arith nsimplify in *
           | _ => progress push_nat2n_all
           | _ => rewrite N.add_assoc in *
           | _ => rewrite N.mul_assoc in *
           | H : _ |- _ => rewrite (N.pow_add_r _ _ (N.of_nat PAGE_LEVEL_BITS)) in H
           | H : _ |- _ => rewrite <-(N.div_div _ _ (2 ^ PAGE_LEVEL_BITS)) in H by solver
           | H : context [((?w / ?x + ?y) * ?z * ?x)%N] |- _ =>
             replace ((w / x + y) * z * x)%N with (z * (x * (w / x + y)))%N in H by solver;
               rewrite (N.mul_add_distr_l x) in H; rewrite N.mul_div in H by solver;
                 apply N.div_lt_upper_bound in H
           | H : (?x < ?y)%N, H' : ?x = ?z |- _ => rewrite H' in H
           | _ => solver
           end.
    (* some additional pose proofs let [solver] solve the goal *)
    match goal with
    | |- context [(?y mod ?m)%N] =>
      pose proof N.mod_le y m ltac:(auto);
        pose proof N.mod_bound_pos y m ltac:(auto) ltac:(solver);
        solver
    end.
  Qed.

  Lemma mm_index_start_of_next_block a level :
    (mm_start_of_next_block a (mm_entry_size level) < mm_level_end a level)%N ->
    mm_index (mm_start_of_next_block a (mm_entry_size level)) level
    = S (mm_index a level).
  Proof.
    intros. cbv [mm_index].
    autorewrite with pull_n2nat; apply Nnat.N2Nat.inj_iff.
    rewrite mm_start_of_next_block_shift.
    autorewrite with bits2arith nsimplify.
    rewrite <-N.add_mod_idemp_l by solver.
    rewrite N.mod_small by auto using level_bits_small.
    solver.
  Qed.

  Lemma mm_start_of_next_block_lt a block_size :
    N.is_power_of_two (N.of_nat block_size) ->
    (a < mm_start_of_next_block a block_size)%N.
  Proof.
    cbv [mm_start_of_next_block]; intros.
    autorewrite with bits2arith.
    assert_nmod_bounds. solver.
  Qed.

  (*** Proofs about [mm_level_end] ***)

  Lemma mm_level_end_lt a level : (a < mm_level_end a level)%N.
  Proof.
    cbv [mm_level_end]; intros.
    autorewrite with bits2arith push_nmul.
    rewrite N.mul_div' by auto.
    assert_nmod_bounds. solver.
  Qed.

  Lemma mm_level_end_le a level : (a <= mm_level_end a level)%N.
  Proof. intros; auto using mm_level_end_lt. Qed.

  Lemma mm_level_end_high_eq a b level :
    (a / mm_entry_size (level + 1))%N = (b / mm_entry_size (level + 1))%N <->
    mm_level_end a level = mm_level_end b level.
  Proof.
    cbv [mm_level_end]; intros.
    autorewrite with bits2arith pull_nat2n.
    rewrite <-mm_entry_size_eq.
    rewrite N.mul_cancel_r by (apply N.neq_0_lt_0; auto using mm_entry_size_pos).
    split; solver.
  Qed.

  Lemma mm_level_end_eq a b c level :
    mm_level_end a level = mm_level_end c level ->
    (a <= b <= c)%N ->
    mm_level_end b level = mm_level_end a level.
  Proof.
    rewrite <-!mm_level_end_high_eq; intros.
    pose proof mm_entry_size_pos (level + 1).
    apply N.mul_cancel_l with (p:=mm_entry_size (level + 1));
      try solver; [ ].
    rewrite (N.div_between_eq a b c); solver.
  Qed.

  Lemma mm_level_end_start_of_next_block_previous a b level :
    (0 < b < mm_entry_size level)%N ->
    mm_level_end (mm_start_of_next_block a (mm_entry_size level) - b) level = mm_level_end a level.
  Proof.
    intros; apply mm_level_end_high_eq.
    rewrite mm_start_of_next_block_eq' by auto using mm_entry_size_power_two.
    rewrite mm_entry_size_step. push_nat2n.
    rewrite <-!N.div_div by solver.
    rewrite N.div_sub_small by solver.
    nsimplify. solver.
  Qed.

  (*** Proofs about [mm_index] ***)

  Lemma mm_index_le_mono a b level :
    (a <= b)%N ->
    mm_level_end a level = mm_level_end b level ->
    mm_index a level <= mm_index b level.
  Proof.
    rewrite <-mm_level_end_high_eq; intros.
    rewrite mm_entry_size_step, mm_entry_size_eq in *.
    push_nat2n_all.
    rewrite <-!N.div_div in * by auto.
    cbv [mm_index]. apply N.to_nat_le_iff.
    autorewrite with bits2arith nsimplify.
    rewrite !N.mod_eq by (apply N.pow_nonzero; solver).
    match goal with
    | H : (_ / _ = _ / _)%N |- _ => rewrite H
    end.
    apply N.sub_le_mono_r; solver.
  Qed.

  Lemma mm_index_capped level (a : ptable_addr_t) i :
    i < 2 ^ PAGE_LEVEL_BITS ->
    (N.to_nat a < i * mm_entry_size level) ->
    mm_index a level < i.
  Proof.
    cbv [mm_index]; intros.
    rewrite <-(Nnat.Nat2N.id i). apply N.to_nat_lt_iff.
    autorewrite with bits2arith nsimplify pull_nat2n.
    rewrite <-mm_entry_size_eq.
    pose proof mm_entry_size_pos level.
    assert (a < N.of_nat i * N.of_nat (mm_entry_size level))%N by solver.
    assert (N.of_nat i < N.of_nat (2 ^ PAGE_LEVEL_BITS))%N by solver.
    assert (a < N.of_nat (mm_entry_size level) * N.of_nat (2 ^ PAGE_LEVEL_BITS))%N
      by (eapply N.lt_trans; [eassumption|]; rewrite N.mul_comm;
          apply N.mul_lt_mono_pos_l; auto).
    rewrite N.mod_small by (apply N.div_lt_upper_bound; solver).
    apply N.div_lt_upper_bound; solver.
  Qed.

  Lemma mm_index_eq a b level :
    (a <= b)%N ->
    mm_level_end a level = mm_level_end b level ->
    (mm_index a level <= mm_index b level)%N ->
    (b < mm_start_of_next_block a (mm_entry_size level))%N ->
    mm_index b level = mm_index a level.
  Proof.
    intros; apply Nat.le_antisymm;
      [ | solve [auto using mm_index_le_mono] ].
    pose proof mm_entry_size_gt_1 level.
    let H := fresh in
    assert (b <= mm_start_of_next_block a (mm_entry_size level) - 1)%N as H by lia;
      apply mm_index_le_mono with (level:=level) in H.
    { rewrite mm_index_start_of_next_block_previous in *; solver. }
    { rewrite mm_level_end_start_of_next_block_previous; solver. }
  Qed.

  Lemma address_matches_indices_root root_level a flags :
    is_root root_level flags ->
    address_matches_indices
      (uintvaddr_to_uintpaddr a) (mm_index a root_level :: nil) (stage_from_flags flags).
  Proof.
    intro H. cbv [is_root] in H; rewrite H; intros.
    cbv [address_matches_indices indices_from_address].
    rewrite seq_snoc, rev_unit, Nat.add_0_l.
    cbn [length firstn map].
    rewrite index_of_uintvaddr by solver.
    cbv [mm_index]. autorewrite with bits2arith nsimplify.
    rewrite mm_max_level_eq.
    apply f_equal2; try solver; [ ].
    repeat (f_equal; try solver).
  Qed.
  Hint Resolve address_matches_indices_root.

  (*** Proofs about [mm_free_page_pte] ***)

  (* mm_free_page_pte doesn't change the state *)
  Lemma mm_free_page_pte_represents (conc : concrete_state) pte level ppool :
    fst (mm_free_page_pte conc pte level ppool) = conc.
  Proof.
    autounfold.
    generalize dependent conc. generalize dependent pte.
    generalize dependent ppool.
    induction level; intros; cbn [mm_free_page_pte];
      repeat match goal with
             | _ => simplify_step
             | _ => apply fold_right_invariant; [ | solver ]
             end.
  Qed.

  (*** Proofs about [mm_replace_entry] ***)

  (* mm_replace_entry doesn't change the state (it does in C, but in the Coq
     translation it returns a new table to the caller and the caller updates the
     state) *)
  Lemma mm_replace_entry_represents
        (conc : concrete_state)
        begin t pte_index new_pte level flags ppool :
    snd (fst (mm_replace_entry
                conc begin t pte_index new_pte level flags ppool)) = conc.
  Proof.
    autounfold; cbv [mm_replace_entry].
    repeat match goal with
           | _ => simplify_step
           | _ => rewrite mm_free_page_pte_represents
           end.
  Qed.

  (*** Proofs about [mm_populate_table_pte] ***)

  (* mm_populate_table_pte doesn't change the state (it does in C, but in the Coq
     translation it returns a new table to the caller and the caller updates the
     state) *)
  Lemma mm_populate_table_pte_represents
        (conc : concrete_state)
        begin t pte_index level flags ppool :
    snd (fst (mm_populate_table_pte
                conc begin t pte_index level flags ppool)) = conc.
  Proof.
    autounfold; cbv [mm_populate_table_pte].
    repeat match goal with
           | _ => simplify_step
           | _ => rewrite mm_replace_entry_represents
           end.
  Qed.

  (*** Proofs about [mm_map_level] ***)

  (* mm_map_level doesn't change the state (it does in C, but in the Coq
     translation it returns a new table to the caller and the caller updates the
     state) *)
  Lemma mm_map_level_represents
        (conc : concrete_state)
        begin end_ pa attrs table level flags ppool :
    (snd (fst (mm_map_level
                 conc begin end_ pa attrs table level flags ppool))) = conc.
  Proof.
    autounfold; cbv [mm_map_level].
    repeat match goal with
           | _ => simplify_step
           | _ => apply while_loop_invariant; [ | solver ]
           | _ => rewrite mm_free_page_pte_represents
           | _ => rewrite mm_replace_entry_represents
           | _ => rewrite mm_populate_table_pte_represents
           end.
  Qed.

  Lemma mm_map_level_table_attrs conc begin end_ pa attrs table level
        flags ppool ptr idxs :
    let ret :=
        mm_map_level conc begin end_ pa attrs table level flags ppool in
    let success := fst (fst (fst ret)) in
    let new_table := snd (fst (fst ret)) in
    let conc' := snd (fst ret) in
    let ppool' := snd ret in
    conc.(ptable_deref) ptr = table ->
    has_location_in_state conc ptr idxs ->
    level <= max_level (stage_from_flags flags) ->
    has_uniform_attrs conc.(ptable_deref) idxs new_table level attrs begin end_ (stage_from_flags flags).
  Admitted.

  (* TODO: make locations_exclusive take a list of mpools so we can include the
     fact that the local pool doesn't overlap with active tables -- this will be
     needed when we eventually call mpool_fini and add those locations to the
     global freelist *)
  (* states that mm_map_level returns a table such that *)
  Lemma mm_map_level_locations_exclusive conc begin end_ pa attrs table level
        flags ppool ptr :
    let ret :=
        mm_map_level conc begin end_ pa attrs table level flags ppool in
    let success := fst (fst (fst ret)) in
    let new_table := snd (fst (fst ret)) in
    let conc' := snd (fst ret) in
    let ppool' := snd ret in
    conc.(ptable_deref) ptr = table ->
    locations_exclusive
      (ptable_deref (reassign_pointer conc ptr new_table))
      (map vm_ptable vms) hafnium_ptable conc.(api_page_pool).
  Admitted. (* TODO *)

  Lemma mm_map_level_reassign_pointer conc begin end_ pa attrs table level
        flags ppool ptr :
    let ret :=
        mm_map_level conc begin end_ pa attrs table level flags ppool in
    let success := fst (fst (fst ret)) in
    let new_table := snd (fst (fst ret)) in
    let conc' := snd (fst ret) in
    let ppool' := snd ret in
    conc.(ptable_deref) ptr = table ->
    is_valid (reassign_pointer conc ptr new_table).
  Proof.
    cbv [is_valid]; basics.
    cbn [api_page_pool reassign_pointer].
    auto using mm_map_level_locations_exclusive.
  Qed.

  (* TODO: might want a nicer reasoning framework for this *)
  (* mm_map_level doesn't alter the global locations of any pointers above the
     level at which it operates *)
  Lemma mm_map_level_index_sequences
        c begin end_ pa attrs root_ptr ptr level flags ppool :
    is_valid c ->
    let ret := mm_map_level
                 c begin end_ pa attrs (ptable_deref c ptr) level flags ppool in
    let table := snd (fst (fst ret)) in
    In ptr (mm_page_table_from_pa root_ptr) ->
    forall ptr' root_ptable,
      In ptr' (mm_page_table_from_pa root_ptr) ->
      In root_ptable all_root_ptables ->
      index_sequences_to_pointer c.(ptable_deref) ptr' root_ptable =
      index_sequences_to_pointer
        (reassign_pointer c ptr table).(ptable_deref) ptr' root_ptable.
  Admitted. (* TODO *)

  (*** Helpers for [mm_map_root] proofs ***)

  (* table pointers that come before the index of [begin] don't contain any
     addresses in the range [begin...end_) *)
  Lemma root_mm_index_out_of_range_low
        conc begin end_ root_level root_ptable flags :
    ptable_is_root root_ptable flags ->
    is_root root_level flags ->
    forall i,
      i <= mm_index begin root_level ->
      Forall (fun ptr => no_addresses_in_range (ptable_deref conc) ptr begin end_)
             (firstn i (mm_page_table_from_pa root_ptable.(root))).
  Admitted. (* TODO *)

  (* table pointers that come after the index of [end_ - 1] don't contain any
     addresses in the range [begin...end_) *)
  Lemma root_mm_index_out_of_range_high
        conc begin end_ root_level root_ptable flags:
    ptable_is_root root_ptable flags ->
    is_root root_level flags ->
    forall i,
      mm_index (end_ - 1) root_level < i ->
      Forall (fun ptr => no_addresses_in_range (ptable_deref conc) ptr begin end_)
             (skipn i (mm_page_table_from_pa root_ptable.(root))).
  Admitted. (* TODO *)

  (* dumb wrapper for one of the invariants so it doesn't get split too early *)
  Definition is_begin_or_block_start
             (start_begin begin : ptable_addr_t) root_level : Prop :=
      (begin = start_begin \/ is_start_of_block begin (mm_entry_size root_level)).

  (* dumb wrapper for one of the invariants so it doesn't get split too early *)
  Definition table_index_expression (begin end_ : ptable_addr_t) root_level : size_t :=
    if N.lt_le_dec begin end_
    then
      (* if we're still looping through, we know that we haven't passed the end of
         the table, so we're still in sync with [begin]*)
      mm_index begin root_level
    else
      (* if begin >= end, we're finishing the loop, and we can't guarantee that
         the index of [begin] hasn't overflowed back to 0; instead, we phrase
         things in terms of the index of the very last address we need to
         process, [end_ - 1], and say we're one index beyond that. *)
      S (mm_index (end_ - 1) root_level).

  Definition mm_map_root_loop_invariant
             start_abst start_conc t_ptrs start_begin end_ attrs root_level
             (state : concrete_state * ptable_addr_t * size_t * bool * mpool)
    : Prop :=
    let '(s, begin, table_index, failed, ppool) := state in
    (* Either we failed, or... *)
    (failed = true \/
     (* table_index stays in sync with [begin] *)
     (table_index = table_index_expression begin end_ root_level
      (* ...and [begin] increases monotonically *)
      /\ (start_begin <= begin)%N
      (* ...and the concrete state stays valid *)
      /\ is_valid s
      (* ..and [begin] is either equal to its starting value or is the start
         of a block *)
      /\ is_begin_or_block_start start_begin begin root_level
      (* ...and we don't add/remove/change references to the root page tables  *)
      /\ (Forall (fun t_ptr =>
                    Forall
                      (fun root_ptable =>
                         index_sequences_to_pointer
                           start_conc.(ptable_deref) t_ptr root_ptable
                         = index_sequences_to_pointer
                             s.(ptable_deref) t_ptr root_ptable)
                      all_root_ptables)
                 t_ptrs)
      (* ...and our concrete state is represented by the abstract state that
         corresponds to processing the first [table_index] entries of the original list *)
      /\ (represents
            (fold_left
               (fun abst t_ptr =>
                  abstract_reassign_pointer
                    abst start_conc t_ptr attrs start_begin end_)
               (firstn table_index t_ptrs)
               start_abst)
            s))).

  (*** Proofs about [mm_map_root] ***)

  (* if the begin address is >= the end address, the abstract state doesn't
     change. *)
  Lemma mm_map_root_range_invalid
        (conc : concrete_state)
        t begin end_ attrs root_level flags ppool :
    let ret :=
        mm_map_root
          conc t begin end_ attrs root_level flags ppool in
    let conc' := snd (fst ret) in
    (end_ <= begin)%N ->
    forall abst,
      represents abst conc ->
      represents abst conc'.
  Proof.
    cbv [mm_map_root];
      repeat match goal with
             | _ => progress simplify_step
             | _ => rewrite while_loop_noop; [solver|]
             | _ => apply N.ltb_ge; solver
             end.
  Qed.

  (* TODO:
     This proof says only that if success = true and commit = true
     then the abstract state changed. We need two more proofs for full
     correctness; one saying that if commit = false, the state is
     unchanged, and another saying that if success = true and commit =
     false, then success = true when the function is run again on the
     (unchanged) output state. *)
  Lemma mm_map_root_represents_commit
        (conc : concrete_state)
        t begin end_ attrs root_level flags ppool :
    let ret :=
        mm_map_root
          conc t begin end_ attrs root_level flags ppool in
    let ppool' := snd ret in
    let conc' := snd (fst ret) in
    let success := fst (fst ret) in
    let begin_index := mm_index begin root_level in
    success = true ->
    ((flags & MM_FLAG_COMMIT) != 0)%N = true ->
    (* before calling mm_map_root, we have rounded end_ up to the nearest page,
       and we have capped it to not go beyond the end of the table *)
    (N.to_nat end_ <= mm_root_table_count flags * mm_entry_size root_level) ->
    (* we need to know we're actually at the root level *)
    is_root root_level flags ->
    ptable_is_root t flags ->
    (* and that [begin] and [end_ - 1] are on the same level *)
    mm_level_end begin root_level = mm_level_end (end_ - 1) root_level ->
    forall abst,
      represents abst conc ->
      represents (fold_left
                    (fun abst t_ptr =>
                       abstract_reassign_pointer
                         abst conc t_ptr attrs begin end_)
                    (mm_page_table_from_pa t.(root))
                    abst)
                 conc'.
  Proof.
    (* get rid of the [let]s and [intros] the preconditions *)
    cbv zeta; simplify.

    (* first, dispose of the easy case in which [end_ <= begin] *)
    basics.
    destruct (N.lt_ge_cases begin end_);
      [|
       apply mm_map_root_range_invalid; auto; [ ];
       apply fold_left_invariant; [|solver];
       solve [eauto using abstract_reassign_pointer_trivial,
              represents_proper_abstr] ].

    (* useful facts about root_level *)
    pose proof (root_pos root_level flags ltac:(auto)).
    pose proof (root_le_max_level root_level flags ltac:(auto)).

    (* unfold [mm_map_root] to begin the real work *)
    cbv [mm_map_root] in *; simplify.

    (* use [while_loop_invariant] with [mm_map_root_loop_invariant] as the
       invariant *)
    let begin_index := constr:(mm_index begin root_level) in
    let t_ptrs := constr:(mm_page_table_from_pa t.(root)) in
    match goal with
    | |- context [@while_loop _ ?iter ?cond ?start ?body] =>
      assert (mm_map_root_loop_invariant
                abst conc t_ptrs begin end_ attrs root_level
                (@while_loop _ iter cond start body));
        [ apply while_loop_invariant | ]
    end;
      cbv [mm_map_root_loop_invariant] in *;
      rewrite ?mm_map_level_represents; [ | | ].

    (***
      At this point we have three subgoals:
       1. if the invariant holds at the start of the loop body, then it holds on
          the new state at the end
       2. the invariant holds for the start state
       3. if the invariant holds by the end of the loop, it implies our original
          goal
     ***)

    { (* Subgoal 1 (main case) : prove invariant holds over step *)

      (* conclude that mm_map_level succeeded *)
      simplify; repeat inversion_bool; [ ].
      right; rewrite !mm_map_level_represents.

      (* find the current [begin] and assert its properties *)
      match goal with
      | H : is_begin_or_block_start _ ?x _ |- _ =>

        (* the level end hasn't changed *)
        assert (mm_level_end x root_level = mm_level_end (end_ - 1) root_level)
          by (rewrite (mm_level_end_eq begin n (end_ - 1)) by solver; solver);

          (* its index is in between the start and end addresses' indices *)
          assert (mm_index begin root_level <= mm_index x root_level <= mm_index (end_ - 1) root_level)
          by (split; apply mm_index_le_mono; solver);

          (* the index doesn't go past the end of the table *)
          assert (mm_index x root_level < length (mm_page_table_from_pa t.(root)))
            by (erewrite mm_page_table_from_pa_length by eauto;
                apply mm_index_capped; [|solver]; apply mm_root_table_count_upper_bound)
      end.

      (* split into the invariant clauses *)
      simplify.

      { (* table_index = if (begin < end_)
                         then mm_index begin root_level
                         else mm_index end_ root_level *)
        (* TODO: clean up *)
        cbv [table_index_expression] in *; simplify; [ | ].
        pose proof mm_level_end_lt (end_ - 1) root_level.
        { rewrite mm_index_start_of_next_block; try solver; [ ].
          match goal with H : mm_level_end _ ?l = mm_level_end _ ?l |- _ =>
                          rewrite H end;
            solver. }
        {
          apply eq_S, eq_sym.
          apply mm_index_eq; solver. } }
      { (* start_begin <= begin *)
        match goal with
          |- (_ <= mm_start_of_next_block ?x _)%N => transitivity x; [solver|]
        end.
        apply N.lt_le_incl.
        apply mm_start_of_next_block_lt;
          auto using mm_entry_size_power_two. }
      { (* is_valid s *)
        cbv [table_index_expression] in *; simplify; [ ].
        apply represents_valid_concrete.
        destruct abst; eexists. (* [destruct abst] is so [eexist] doesn't use [abst] *)
        eapply reassign_pointer_represents; eauto; [ | ].
        { apply mm_map_level_locations_exclusive; solver. }
        { apply has_uniform_attrs_reassign_pointer;
            try apply mm_map_level_reassign_pointer;
            try eapply mm_map_level_table_attrs; solver. } }
      { (* is_begin_or_block_start start_begin begin  *)
        cbv [is_begin_or_block_start]. right.
        apply mm_start_of_next_block_is_start;
          auto using mm_entry_size_power_two. }
      { (* index sequences don't change *)
        cbv [table_index_expression] in *; simplify; [ ].
        apply Forall_forall; intros.
        apply Forall_forall; intros.
        repeat match goal with
               | H : Forall _ _ |- _ =>
                 rewrite Forall_forall in H; specialize (H _ ltac:(eassumption));
                   try rewrite H
               end.
        eapply mm_map_level_index_sequences; eauto; [ ].
        apply In_nth_default; solver. }
      { (* represents step *)
        cbv [table_index_expression] in *; simplify; [ ].

        rewrite firstn_snoc with (d:=null_pointer)
          by (autorewrite with push_length; lia).
        rewrite fold_left_app.
        cbn [fold_left].

        (* swap out starting concrete state for current one *)
        match goal with
          |- represents (abstract_reassign_pointer _ ?conc _ _ _ _) (reassign_pointer ?c _ _) =>
          rewrite abstract_reassign_pointer_change_concrete with (conc':=c)
            by
              repeat match goal with
                     | H : Forall _ _ |- _ => rewrite Forall_forall in H; apply H
                     | _ => apply In_nth_default
                     | _ => solver
                     end
        end.

        eapply reassign_pointer_represents with (level := root_level - 1);
          try apply mm_map_level_locations_exclusive; try solver; [ ].
        apply has_uniform_attrs_reassign_pointer;
          try auto using mm_map_level_reassign_pointer; try solver; [ ].
        match goal with
        | H : is_begin_or_block_start ?b ?x ?lvl |- _ =>
          destruct H; [ subst;
                        eapply mm_map_level_table_attrs; solver | ]
        end.
        eapply has_uniform_attrs_block_start; try solver; [ ].
        eapply mm_map_level_table_attrs; solver. } }

    { (* Subgoal 2 : invariant holds at start *)
      right.
      cbv [table_index_expression] in *; simplify; [ | | | ].
      { eauto using represents_valid_concrete. }
      { cbv [is_begin_or_block_start]; simplify. }
      { apply Forall_forall; intros.
        apply Forall_forall; intros.
        reflexivity. }
      { eapply represents_proper_abstr; [|solver].
        apply abstract_reassign_pointer_low.
        eapply root_mm_index_out_of_range_low; solver. } }

    { (* Subgoal 3 :invariant implies correctness *)

      (* conclude that mm_map_root succeeded *)
      repeat inversion_bool; simplify; [ ].

      match goal with
      | |- context [@while_loop _ ?iter ?cond ?st ?body] =>

        (* use  [while_loop_completed] to say that we must have reached our end
           condition and therefore [begin >= end_] *)
          assert (cond (@while_loop _ iter cond st body) = false);
            [ apply (while_loop_completed iter cond body
                                          (fun '(_,_,_,failed,_) => negb failed)
                                          (fun '(_,begin,_,_,_) => N.to_nat begin)
                                          (N.to_nat end_)) | ];

            (* store the loop result as a varaible and then "forget" the
               variable's value; we don't need that information (that our result
               was from a while loop) any more, and disposing of it speeds up
               proofs *)
            let H := fresh in
            let RET := fresh "RET" in
            remember (@while_loop _ iter cond st body) as RET eqn:H;
              clear H
      end;
        (* prove all [while_loop_completed]'s preconditions *)
        repeat match goal with
               | _ => progress simplify_step
               | _ => apply N.to_nat_ltb
               | |- N.to_nat _ < N.to_nat _ => apply N.to_nat_lt_iff
               | _ => rewrite Nnat.N2Nat.inj_sub; solver
               | _ => solve [auto using mm_start_of_next_block_lt,
                             mm_entry_size_power_two]
               end; [ ].

      (* prove that the abstract state we have from the invariant is equivalent
         to the one in the goal *)
      match goal with
      | H : represents ?x ?c |- represents ?y ?c =>
        apply (represents_proper_abstr x y c); [|solver]
      end.
      cbv [table_index_expression is_begin_or_block_start] in *.
      apply abstract_reassign_pointer_high;
        repeat match goal with
               | _ => progress simplify
               | _ => inversion_bool
               | _ => eapply root_mm_index_out_of_range_high
               | _ => solver
               end. }
  Qed.

  (* placeholder; later there will be actual expressions for the new abstract
     states *)
  Axiom TODO : @abstract_state paddr_t nat.

  (*** Proofs about [mm_ptable_identity_update] ***)

  Lemma mm_ptable_identity_update_represents
        (conc : concrete_state)
        t pa_begin pa_end attrs flags ppool :
    forall abst,
      represents abst conc ->
      represents TODO
                 (snd (fst (mm_ptable_identity_update
                              conc t pa_begin pa_end attrs flags ppool))).
  Admitted.

  (*** Proofs about [mm_identity_map] ***)

  Lemma mm_identity_map_represents
        (conc : concrete_state)
        begin end_ mode ppool :
    preserves_represents_valid
      (fun conc => snd (fst (mm_identity_map conc begin end_ mode ppool))).
  Admitted.

  (*** Proofs about [mm_defrag] ***)

  Lemma mm_defrag_represents
        (conc : concrete_state)
        ppool :
    preserves_represents_valid
      (fun conc => fst (mm_defrag conc ppool)).
  Admitted.

  (*** Proofs about [mm_unmap] ***)

  Lemma mm_unmap_represents
        (conc : concrete_state)
        begin end_ ppool :
    preserves_represents_valid
      (fun conc => snd (fst (mm_unmap conc begin end_ ppool))).
  Admitted.
End Proofs.
