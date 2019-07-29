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

  (*** Generally useful lemmas ***)

  Lemma root_pos level flags : is_root level flags -> 0 < level.
  Proof. cbv [is_root]; simplify. Qed.

  Lemma ptable_is_root_In (t : mm_ptable) (flags : int) :
    ptable_is_root t flags ->
    In t all_root_ptables.
  Proof.
    cbv [all_root_ptables ptable_is_root]; intros.
    break_match; subst; auto using in_eq, in_cons.
  Qed.

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
    rewrite N.shiftl_1_l.
    (* TODO : clean this up with a push_Nat2N tactic *)
    apply Nnat.Nat2N.inj_iff.
    rewrite Nnat.N2Nat.id.
    rewrite Nat2N.inj_pow.
    rewrite Nnat.Nat2N.inj_add.
    rewrite Nnat.Nat2N.inj_mul.
    reflexivity.
  Qed.

  Lemma mm_entry_size_power_two level :
    N.is_power_of_two (N.of_nat (mm_entry_size level)).
  Proof.
    cbv [mm_entry_size].
    rewrite Nnat.N2Nat.id.
    apply N.shiftl_power_two.
  Qed.

  Lemma mm_entry_size_gt_1 level : (1 < mm_entry_size level)%N.
  Proof.
    intros; rewrite mm_entry_size_eq.
    pose proof PAGE_BITS_pos.
    rewrite Nat2N.inj_pow.
    change 1%N with (2 ^ 0)%N.
    change (N.of_nat 2) with 2%N.
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

  Lemma mm_start_of_next_block_eq a level :
    mm_start_of_next_block a (mm_entry_size level)
    = (a + mm_entry_size level - a mod mm_entry_size level)%N.
  Proof.
    cbv [mm_start_of_next_block mm_entry_size].
    repeat progress rewrite ?Nnat.N2Nat.inj_add, ?Nnat.N2Nat.inj_mul, ?Nnat.N2Nat.id.
    rewrite N.and_not by auto using N.shiftl_power_two.
    rewrite N.mod_add_cancel_r by (rewrite N.shiftl_eq_0_iff; lia).
    rewrite N.shiftl_1_l.
    reflexivity.
  Qed.

  Lemma mm_start_of_next_block_eq' a level :
    mm_start_of_next_block a (mm_entry_size level)
    = ((a / mm_entry_size level + 1) * mm_entry_size level)%N.
  Proof.
    rewrite mm_start_of_next_block_eq.
    pose proof mm_entry_size_pos level.
    pose proof N.mod_bound_pos a (mm_entry_size level).
    match goal with |- context [(?a + ?m - ?a mod ?m)%N] =>
                    replace (a + m - a mod m)%N with (m + (a - a mod m))%N
                      by (rewrite N.mod_eq; solver);
                      rewrite <-(N.mul_div a m) by solver
    end.
    rewrite N.mul_add_distr_r, N.mul_1_l.
    rewrite (N.mul_comm (mm_entry_size level)).
    apply N.add_comm.
  Qed.

  Lemma mm_start_of_next_block_is_start a block_size :
    is_start_of_block (mm_start_of_next_block a block_size) block_size.
  Admitted. (* TODO *)

  Lemma mm_start_of_next_block_shift a level :
    (mm_start_of_next_block a (mm_entry_size level)
                            >> (PAGE_BITS + level * PAGE_LEVEL_BITS))%N =
    ((a >> (PAGE_BITS + level * PAGE_LEVEL_BITS)) + 1)%N.
  Proof.
    intros. pose proof PAGE_BITS_pos.
    cbv [mm_start_of_next_block mm_entry_size].
    rewrite !Nnat.N2Nat.id, N.shiftr_land, N.lnot_shiftr.
    rewrite N.shiftr_eq_0 with (a:=((_ << _) - 1)%N) by
        (rewrite N.sub_1_r, N.shiftl_1_l, N.log2_pred_pow2 by lia; lia).
    rewrite N.lnot_0_l.
    match goal with
    | |- context [((_ + (_ << ?x)) >> ?x)%N] =>
      pose proof (N.log2_add_shiftl_1 a x);
        assert ((1 << x) <> 0)%N by (rewrite N.shiftl_eq_0_iff; lia)
    end.
    rewrite N.land_ones_low by (rewrite N.log2_shiftr, N.size_log2 by lia; lia).
    rewrite !N.shiftr_div_pow2, !N.shiftl_mul_pow2.
    rewrite N.div_add by (apply N.pow_nonzero; lia).
    lia.
  Qed.

  Lemma mm_index_start_of_next_block_previous a b level :
    (0 < b <= mm_entry_size level)%N ->
    mm_index (mm_start_of_next_block a (mm_entry_size level) - b) level = mm_index a level.
  Proof.
    (* TODO: clean up this proof! *)
    cbv [mm_index]; intros.
    apply Nnat.N2Nat.inj_iff.
    rewrite !N.land_ones' by auto using N.shiftl_power_two.
    rewrite N.shiftl_1_l, N.log2_pow2 by lia.
    rewrite mm_start_of_next_block_eq'.
    cbv [mm_entry_size] in *.
    rewrite Nnat.N2Nat.id in *.
    remember (PAGE_BITS + level * PAGE_LEVEL_BITS)%N.
    rewrite !N.shiftl_1_l in *.
    rewrite !N.shiftr_div_pow2.
    rewrite N.div_sub_small by solver.
    f_equal; lia.
  Qed.

  (* helper lemma for mm_index_start_of_next_block *)
  Lemma level_bits_small a level :
    (mm_start_of_next_block a (mm_entry_size level) < mm_level_end a level)%N ->
    ((a >> (PAGE_BITS + level * PAGE_LEVEL_BITS)) mod 2 ^ PAGE_LEVEL_BITS + 1 < 2 ^ PAGE_LEVEL_BITS)%N.
  Proof.
    (* TODO : clean up this proof! *)
    cbv [mm_level_end]; intros.
    repeat progress rewrite ?Nnat.Nat2N.inj_add, ?Nnat.Nat2N.inj_mul in *.
    change (N.of_nat 1) with 1%N in *.
    replace (2 ^ PAGE_LEVEL_BITS)%N with
        ((1 << (PAGE_BITS + (level + 1) * PAGE_LEVEL_BITS)) >> (PAGE_BITS + level * PAGE_LEVEL_BITS))%N by
        (rewrite N.shiftr_shiftl_l, N.shiftl_1_l by lia; f_equal; lia).
    replace (PAGE_BITS + (level + 1) * PAGE_LEVEL_BITS)%N with
        (PAGE_BITS + level * PAGE_LEVEL_BITS + PAGE_LEVEL_BITS)%N in * by lia.
    apply N.shiftr_lt_shiftl_mono in H.
    rewrite <-!(N.shiftr_shiftr _ _ (N.of_nat PAGE_LEVEL_BITS)) in H.
    rewrite mm_start_of_next_block_shift in H.
    rewrite N.shiftr_shiftl_l by lia.
    match goal with
      |- context [ (1 << ?n)%N ] => replace n with (N.of_nat PAGE_LEVEL_BITS) by lia
    end.
    remember (a >> N.of_nat PAGE_BITS + N.of_nat level * N.of_nat PAGE_LEVEL_BITS)%N as A.
    remember (N.of_nat PAGE_LEVEL_BITS) as N.
    assert ((1 << N) <> 0)%N by (rewrite N.shiftl_eq_0_iff; lia).
    pose proof (N.mod_bound_pos (A + 1)%N (1 << N)%N).
    assert (A mod (1 << N) + 1 = (A + 1) mod (1 << N))%N; [|lia].
    rewrite !N.mod_eq by solver.
    rewrite N.shiftl_1_l, <-!N.shiftr_div_pow2.
    let H := fresh in
    assert (((A + 1) >> N) = (A >> N))%N as H
        by (apply N.le_antisymm; try solver; apply N.shiftr_le_mono_r; solver);
      rewrite H in *.
    rewrite <-N.add_sub_swap by (rewrite N.shiftr_div_pow2;
                                 apply N.mul_div_le; apply N.pow_nonzero; lia).
    solver.
  Qed.

  Lemma mm_index_start_of_next_block a level :
    (mm_start_of_next_block a (mm_entry_size level) < mm_level_end a level)%N ->
    mm_index (mm_start_of_next_block a (mm_entry_size level)) level
    = S (mm_index a level).
  Proof.
    intros.
    cbv [mm_index].
    rewrite <-Nnat.N2Nat.inj_succ; apply Nnat.N2Nat.inj_iff.
    rewrite N.shiftl_1_l.
    rewrite !N.land_ones' by auto using N.power_two_trivial.
    rewrite !N.log2_pow2 by lia.
    rewrite mm_start_of_next_block_shift.
    rewrite <-N.add_mod_idemp_l by (apply N.pow_nonzero; lia).
    rewrite N.mod_small by (apply level_bits_small; auto).
    lia.
  Qed.

  Lemma mm_start_of_next_block_lt a block_size :
    N.is_power_of_two (N.of_nat block_size) ->
    (a < mm_start_of_next_block a block_size)%N.
  Proof.
    cbv [mm_start_of_next_block]; intros.
    rewrite N.and_not by auto.
    match goal with
    | |- context [(?x mod ?y)%N] =>
      pose proof
           (N.mod_bound_pos x y ltac:(lia) ltac:(auto using N.power_two_pos))
    end.
    lia.
  Qed.

  Lemma mm_start_of_next_block_level_end a level :
    (mm_start_of_next_block a (mm_entry_size level) <= mm_level_end a level)%N.
  Admitted. (* TODO *)

  (*** Proofs about [mm_level_end] ***)

  Lemma mm_level_end_lt a level : (a < mm_level_end a level)%N.
  Proof.
    cbv [mm_level_end]; intros.
    rewrite N.shiftr_add_shiftl.
    rewrite N.shiftl_1_l.
    match goal with
    | |- context [(2 ^ ?x)%N] =>
      pose proof (N.pow_nonzero 2 x)
    end.
    match goal with
    | |- context [(?x mod ?y)%N] =>
      pose proof (N.mod_bound_pos x y)
    end.
    lia.
  Qed.

  Lemma mm_level_end_le a level : (a <= mm_level_end a level)%N.
  Proof.
    intros; apply N.lt_le_incl; apply mm_level_end_lt.
  Qed.

  Lemma mm_level_end_high_eq a b level :
    (a / mm_entry_size (level + 1))%N = (b / mm_entry_size (level + 1))%N <->
    mm_level_end a level = mm_level_end b level.
  Proof.
    cbv [mm_level_end]; intros.
    rewrite !N.shiftr_div_pow2.
    match goal with |- context [(2 ^ N.of_nat ?x)%N] =>
                    replace (2 ^ N.of_nat x)%N with (N.of_nat (2 ^ x)) by apply Nat2N.inj_pow
    end.
    rewrite <-mm_entry_size_eq.
    rewrite <-N.shiftl_inj_iff.
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
    rewrite mm_start_of_next_block_eq'.
    rewrite mm_entry_size_step.
    rewrite Nnat.Nat2N.inj_mul, Nat2N.inj_pow.
    change (N.of_nat 2) with 2%N.
    pose proof N.pow_nonzero 2%N PAGE_LEVEL_BITS.
    rewrite <-!N.div_div by solver.
    rewrite N.div_sub_small by solver.
    rewrite N.add_sub.
    reflexivity.
  Qed.

  (*** Proofs about [mm_index] ***)

  Lemma mm_index_le_mono a b level :
    (a <= b)%N ->
    mm_level_end a level = mm_level_end b level ->
    mm_index a level <= mm_index b level.
  Admitted. (* TODO *)

  Lemma mm_index_capped level (a : ptable_addr_t) i :
    i < 2 ^ PAGE_LEVEL_BITS ->
    N.to_nat a < i * mm_entry_size level ->
    mm_index a level < i.
  Proof.
    cbv [mm_index mm_entry_size]; intros.
    rewrite !N.shiftl_1_l in *.
    assert (N.to_nat (a >> PAGE_BITS + level * PAGE_LEVEL_BITS)%N < i).
    { rewrite <-(Nnat.Nat2N.id i).
      apply N.to_nat_lt_iff.
      rewrite N.shiftr_div_pow2.
      apply N.div_lt_upper_bound;
        try apply N.pow_nonzero; lia. }
    { rewrite N.land_ones' by auto using N.power_two_trivial.
      rewrite N.log2_pow2 by lia.
      replace (2 ^ PAGE_LEVEL_BITS)%N with (N.of_nat (2 ^ PAGE_LEVEL_BITS))
        by (rewrite Nat2N.inj_pow; reflexivity).
      rewrite N.mod_small by solver.
      solver. }
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
        flags ppool :
    let ret :=
        mm_map_level conc begin end_ pa attrs table (level-1) flags ppool in
    let success := fst (fst (fst ret)) in
    let table := snd (fst (fst ret)) in
    let conc' := snd (fst ret) in
    let ppool' := snd ret in
    has_uniform_attrs conc.(ptable_deref) table (level - 1) attrs begin end_.
  Admitted.

  Lemma mm_map_level_table_attrs_strong conc begin end_ pa attrs table level
        flags ppool :
    let ret :=
        mm_map_level conc begin end_ pa attrs table (level-1) flags ppool in
    let success := fst (fst (fst ret)) in
    let table := snd (fst (fst ret)) in
    let conc' := snd (fst ret) in
    let ppool' := snd ret in
    forall begin',
      mm_index begin' level <= mm_index begin level ->
      has_uniform_attrs conc.(ptable_deref) table (level - 1) attrs begin' end_.
  Admitted.

  Lemma mm_map_level_noncircular c begin end_ pa attrs ptr level flags ppool :
    pointers_ok c ppool ->
    let ret := mm_map_level
                 c begin end_ pa attrs (ptable_deref c ptr) level flags ppool in
    let table := snd (fst (fst ret)) in
    ~ pointer_in_table (ptable_deref c) ptr table.
  Admitted. (* TODO *)

  (* TODO: needs preconditions *)
  Lemma mm_map_level_pointers_ok c begin end_ pa attrs ptr level flags ppool :
    pointers_ok c ppool ->
    let ret := mm_map_level
                 c begin end_ pa attrs (ptable_deref c ptr) level flags ppool in
    let table := snd (fst (fst ret)) in
    let ppool' := snd ret in
    pointers_ok (reassign_pointer c ptr table) ppool'.
  Admitted. (* TODO *)

  (* TODO: might want a nicer reasoning framework for this *)
  (* mm_map_level doesn't alter the global locations of any pointers above the
     level at which it operates *)
  Lemma mm_map_level_index_sequences
        c begin end_ pa attrs root_ptr ptr level flags ppool :
    pointers_ok c ppool ->
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
      (* ...and we never create circular references *)
      /\ pointers_ok s ppool
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
    (* nothing weird and circular going on with pointers *)
    pointers_ok conc ppool ->
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

    (* useful fact about root_level *)
    pose proof (root_pos root_level ltac:(auto)).

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
      { (* pointers_ok s ppool *)
        apply mm_map_level_pointers_ok.
        auto. }
      { (* is_begin_or_block_start start_begin begin  *)
        cbv [is_begin_or_block_start].
        right. apply mm_start_of_next_block_is_start. }
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
        cbv [nth_default_oobe ptable_pointer_oobe oob_value].

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

        apply reassign_pointer_represents with (level := root_level - 1).
        { assumption. }
        { apply has_uniform_attrs_reassign_pointer;
            [ solve [auto using mm_map_level_noncircular] | ].
          auto using mm_map_level_table_attrs_strong. } } }

    { (* Subgoal 2 : invariant holds at start *)
      right.
      cbv [table_index_expression] in *; simplify; [ | | ].
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
