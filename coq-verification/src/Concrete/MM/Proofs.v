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
Require Import Hafnium.Concrete.PageTablesWf.
Require Import Hafnium.Concrete.Parameters.
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

  Ltac simplify_solver :=
    match goal with
    | _ => solver
    | H : break = continue |- _ => cbv [break continue] in H; solver
    | H : continue = break |- _ => cbv [break continue] in H; solver
    end.
  Ltac simplify_no_break_step :=
    match goal with
    | _ => progress basics_no_break
    | _ => progress cbn [fst snd negb] in *
    | p : _ * _ |- _ => destruct p
    | |- context [let '(_,_) := ?x in _] =>
      rewrite (surjective_pairing x)
    | H : context [let '(_,_) := ?x in _] |- _ =>
      rewrite (surjective_pairing x) in H
    end.
  Ltac simplify_step :=
    match goal with
    | _ => simplify_no_break_step
    | _ => simplify_solver
    | H : _ \/ _ |- _ => destruct H
    | _ => break_match
    end.
  Ltac simplify_no_break :=
    repeat match goal with
           | _ => simplify_no_break_step
           | _ => simplify_solver
           end.
  Ltac simplify := repeat simplify_step.

  Ltac invert_is_valid :=
    match goal with
    | H : is_valid ?c |- _ =>
      pose proof H; cbv [is_valid] in H
    end.

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

  Lemma root_matches_stage_from_flags t flags :
    ptable_is_root t flags ->
    root_ptable_matches_stage t (stage_from_flags flags).
  Proof.
    cbv [ptable_is_root stage_from_flags root_ptable_matches_stage].
    break_match; solver.
  Qed.
  Hint Resolve root_matches_stage_from_flags.

  (* if [begin] is the start of the block at the level above, then we can freely
     use a smaller address for [begin], because [attrs_changed_in_range] ignores
     addresses outside of [table]'s range. *)
  Lemma attrs_changed_in_range_block_start
        ptable_deref old_table table level attrs begin end_ idxs stage :
    is_start_of_block begin (mm_entry_size level) ->
    address_matches_indices stage (uintvaddr_to_uintpaddr begin) idxs ->
    forall begin',
      (begin' <= begin)%N ->
      attrs_changed_in_range ptable_deref idxs old_table table level attrs begin end_ stage ->
      attrs_changed_in_range ptable_deref idxs old_table table level attrs begin' end_ stage.
  Admitted.

  (* helper version of attrs_changed_in_range_block_start2 that phrases the
     preconditions slightly differently *)
  Lemma attrs_changed_in_range_block_start2
        ptable_deref old_table table level attrs begin end_ idxs stage :
    address_matches_indices stage (uintvaddr_to_uintpaddr begin) idxs ->
    forall begin',
      begin' = begin \/ is_start_of_block begin (mm_entry_size level) ->
      (begin' <= begin)%N ->
      attrs_changed_in_range ptable_deref idxs old_table table level attrs begin end_ stage ->
      attrs_changed_in_range ptable_deref idxs old_table table level attrs begin' end_ stage.
  Proof.
    simplify; eauto using attrs_changed_in_range_block_start.
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

  Lemma has_location_nth_default deref ppool flags root_ptable i :
    i < length (mm_page_table_from_pa (root root_ptable)) ->
    ptable_is_root root_ptable flags ->
    has_location deref
                 (nth_default_oobe (mm_page_table_from_pa (root root_ptable)) i)
                 (table_loc ppool root_ptable (cons i nil)).
  Proof.
    cbv [ptable_is_root mm_page_table_from_pa]; intros; break_match; basics.
    { apply has_table_loc_stage1. cbv [index_sequences_to_pointer].
      apply index_sequences_to_pointer'_nth_default; solver. }
    { apply has_table_loc_stage2; auto; [ ].
      cbv [index_sequences_to_pointer].
      apply index_sequences_to_pointer'_nth_default; solver. }
  Qed.

  Lemma has_location_in_state_root flags c t i :
    ptable_is_root t flags ->
    i < length (mm_page_table_from_pa (root t)) ->
    has_location_in_state c (nth_default_oobe (mm_page_table_from_pa (root t)) i) (cons i nil).
  Proof.
    cbv [has_location_in_state]. intros; eexists.
    eapply has_location_nth_default; eauto.
  Qed.
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
    apply (N.div_between_eq a b c); solver.
  Qed.

  Lemma mm_level_end_eq2 a b level :
    (a <= b < mm_level_end a level)%N  ->
    mm_level_end b level = mm_level_end a level.
  Proof.
    rewrite <-!mm_level_end_high_eq; intros.
    cbv [mm_level_end] in *.
    autorewrite with bits2arith pull_nat2n in *.
    rewrite <-mm_entry_size_eq in *.
    pose proof mm_entry_size_pos (level + 1).
    match goal with
      | H : (?w <= ?x < ?y * ?z)%N |- _ =>
        pose proof (N.div_lt_upper_bound x z y ltac:(solver) ltac:(solver));
          pose proof (N.div_le_mono w x z ltac:(solver) ltac:(solver))
    end.
    solver.
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

  (* TODO : move *)
  (* if an address a matches a sequence of indices ending in [i], the start of
     the next block at the level corresponding to the last index in the sequence
     will either be the end of the level, or match the same sequence of indices
     except for ending in [S i]. *)
  Lemma mm_start_of_next_block_le_level_end (a : ptable_addr_t) level :
    (mm_start_of_next_block a (mm_entry_size level) <= mm_level_end a level)%N.
  Admitted. (* TODO *)

  Lemma mm_level_end_le_mono_r a level1 level2 :
    level1 <= level2 ->
    (mm_level_end a level1 <= mm_level_end a level2)%N.
  Admitted.

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

  Lemma mm_index_eq2 a b level :
    (b <= a < mm_start_of_next_block b (mm_entry_size level))%N ->
    mm_index a level = mm_index b level.
  Proof.
    intros. pose proof (mm_start_of_next_block_le_level_end b level).
    assert (mm_level_end a level = mm_level_end b level)
      by (apply mm_level_end_eq2; solver).
    apply mm_index_eq; try solver; [ ].
    apply N.to_nat_le_iff. rewrite !Nnat.Nat2N.id.
    apply mm_index_le_mono; solver.
  Qed.

  Lemma address_matches_indices_root root_level a flags :
    is_root root_level flags ->
    address_matches_indices
      (stage_from_flags flags) (uintvaddr_to_uintpaddr a) (mm_index a root_level :: nil).
  Proof.
    intro H. cbv [is_root] in H; rewrite H; intros.
    cbv [address_matches_indices]; autorewrite with push_length; intro i.
    destruct i; basics; [|solver].
    autorewrite with push_nth_default.
    rewrite index_of_uintvaddr by solver.
    rewrite Nat.sub_0_r, mm_max_level_eq.
    cbv [mm_index]. autorewrite with bits2arith nsimplify.
    reflexivity.
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

  Lemma mm_free_page_pte_fallback conc pte level ppool :
    let ret := mm_free_page_pte conc pte level ppool in
    let ppool' := snd ret in
    mpool_fallback ppool' =  mpool_fallback ppool.
  Proof.
    autounfold.
    generalize dependent conc. generalize dependent pte.
    generalize dependent ppool.
    induction level; intros; cbn [mm_free_page_pte];
      repeat match goal with
             | _ => simplify_step
             | _ => rewrite mpool_free_fallback
             | _ => apply fold_right_invariant; [ | solver ]
             end.
  Qed.

  Lemma mm_free_page_pte_exclusive conc pte level ppool :
    let ret := mm_free_page_pte conc pte level ppool in
    let ppool' := snd ret in
    locations_exclusive (ptable_deref conc) ppool ->
    locations_exclusive (ptable_deref conc) ppool'.
  Admitted. (* TODO *)

  Lemma mm_free_page_pte_mpool_exclusive conc pte level ppool ppool2 :
    let ret := mm_free_page_pte conc pte level ppool in
    let ppool' := snd ret in
    locations_exclusive (ptable_deref conc) ppool2 ->
    mpool_exclusive ppool ppool2 ->
    mpool_exclusive ppool' ppool2.
  Admitted. (* TODO *)

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

  Lemma mm_replace_entry_fallback
        conc begin t pte_index new_pte level flags ppool :
    let ret := mm_replace_entry conc begin t pte_index new_pte level flags ppool in
    let ppool' := snd ret in
    mpool_fallback ppool' =  mpool_fallback ppool.
  Proof.
    cbv [mm_replace_entry]; simplify; rewrite mm_free_page_pte_fallback; solver.
  Qed.

  Lemma mm_replace_entry_exclusive
        conc begin ptr pte_index new_pte level flags ppool :
    let t := ptable_deref conc ptr in
    let ret := mm_replace_entry
                 conc begin t pte_index new_pte level flags ppool in
    let new_t := fst (fst ret) in
    let ppool' := snd ret in
    arch_mm_pte_is_table new_pte level = false ->
    locations_exclusive (ptable_deref conc) ppool ->
    locations_exclusive (update_deref (ptable_deref conc) ptr new_t) ppool'.
  Admitted. (* TODO *)

  Lemma mm_replace_entry_mpool_exclusive
        conc begin t pte_index new_pte level flags ppool ppool2 :
    let ret := mm_replace_entry
                 conc begin t pte_index new_pte level flags ppool in
    let ppool' := snd ret in
    (* if none of [ppool2]'s contents are in the page tables *)
    locations_exclusive (ptable_deref conc) ppool2 ->
    (* and they're also not in ppool *)
    mpool_exclusive ppool ppool2 ->
    (* then they're not in the new ppool either *)
    mpool_exclusive ppool' ppool2.
  Admitted. (* TODO *)

  Lemma mm_replace_entry_reassign
        conc begin parent_table_ptr pte_index new_pte level flags ppool :
    let parent_table := ptable_deref conc parent_table_ptr in
    let ret := mm_replace_entry conc begin parent_table pte_index new_pte level
                                flags ppool in
    let new_parent_table := fst (fst ret) in
    let ppool' := snd ret in
    arch_mm_pte_is_table new_pte level = false ->
    is_valid conc ->
    is_valid (reassign_pointer conc parent_table_ptr new_parent_table).
  Admitted. (* TODO *)
  Hint Resolve mm_replace_entry_reassign.

  (*** Proofs about [mm_populate_table_pte] ***)

  (* TODO : move *)
  Hint Resolve mpool_alloc_contains_before.
  Hint Resolve has_table_loc_stage1 has_table_loc_stage2 has_mpool_loc.

  (* TODO : move *)
  Lemma update_page_pool_noop conc :
    update_page_pool conc (api_page_pool conc) = conc.
  Proof. destruct conc; reflexivity. Qed.

  (* mm_populate_table_pte might create tables where there used to be blocks,
     but the concrete state it returns is *equivalent* to the initial state
     because attributes don't change. *)
  Lemma mm_populate_table_pte_equiv
        (conc : concrete_state) begin t pte_index level flags ppool :
    mpool_fallback ppool = Some conc.(api_page_pool) ->
    locations_exclusive (ptable_deref conc) ppool ->
    mpool_exclusive ppool (api_page_pool conc) ->
    is_valid conc ->
    concrete_state_equiv (snd (fst (mm_populate_table_pte
                                      conc begin t pte_index level flags ppool)))
                         conc.
  Proof.
    cbv [mm_populate_table_pte mm_alloc_page_tables]; basics.
    invert_is_valid.
    simplify;
      try match goal with
          | H : mpool_alloc ppool = Some _ |- _ =>
            pose proof H;
              eapply mpool_alloc_fallback in H; [ | solver .. ]
          end;
      repeat match goal with
             | _ => progress simplify
             | _ => progress cbn [hd]
             | _ => inversion_bool
             | Hx : ?a = Some ?x, Hy : ?a = Some ?y |- _ =>
               replace x with y in * by solver; clear Hx
             | _ => rewrite mm_replace_entry_represents
             | _ => rewrite update_page_pool_noop
             | _ => eapply reassign_pointer_fresh; solver
             | _ => eapply reassign_pointer_fresh_fallback_unused
                 with (ppool0:=ppool); solver
             | _ => solver
             end.
  Qed.

  (* mm_populate_table_pte doesn't change the *abstract* state; since it's just
     making tables where there used to be blocks, nothing actually changes *)
  Lemma mm_populate_table_pte_represents
        abst (conc : concrete_state)
        begin t pte_index level flags ppool :
    mpool_fallback ppool = Some conc.(api_page_pool) ->
    locations_exclusive (ptable_deref conc) ppool ->
    mpool_exclusive ppool (api_page_pool conc) ->
    represents abst conc ->
    represents abst
               (snd (fst (mm_populate_table_pte
                            conc begin t pte_index level flags ppool))).
  Proof.
    basics. eapply represents_proper; [ | eassumption ].
    eauto using mm_populate_table_pte_equiv.
  Qed.

  Lemma mm_populate_table_pte_fallback conc begin t pte_index level flags ppool :
    let ret := mm_populate_table_pte conc begin t pte_index level flags ppool in
    let conc' := snd (fst ret) in
    let ppool' := snd ret in
    mpool_fallback ppool = Some conc.(api_page_pool) ->
    mpool_fallback ppool' = Some conc'.(api_page_pool).
  Proof.
    cbv [mm_populate_table_pte mm_alloc_page_tables]; simplify;
      rewrite mm_replace_entry_fallback, mm_replace_entry_represents;
      try match goal with
          | H : mpool_alloc ppool = Some _ |- _ =>
            pose proof H;
              eapply mpool_alloc_fallback in H; [ | solver .. ]
          end; repeat inversion_bool; simplify.
  Qed.

  Lemma mm_populate_table_pte_exclusive
        conc begin parent_table_ptr pte_index level flags ppool :
    let parent_table := ptable_deref conc parent_table_ptr in
    let ret := mm_populate_table_pte conc begin parent_table pte_index level
                                     flags ppool in
    let new_parent_table := fst (fst (fst ret)) in
    let conc' := snd (fst ret) in
    let ppool' := snd ret in
    forall fallback,
      mpool_fallback ppool = Some fallback ->
      locations_exclusive (ptable_deref conc) fallback ->
      locations_exclusive (ptable_deref conc) ppool ->
      locations_exclusive
        (update_deref (ptable_deref conc') parent_table_ptr new_parent_table)
        ppool'.
  Admitted. (* TODO *)

  Lemma mm_populate_table_pte_mpool_exclusive
        conc begin t pte_index level flags ppool :
    let ret := mm_populate_table_pte
                 conc begin t pte_index level flags ppool in
    let conc' := snd (fst ret) in
    let ppool' := snd ret in
    mpool_fallback ppool = Some (api_page_pool conc) ->
    locations_exclusive (ptable_deref conc) (api_page_pool conc) ->
    mpool_exclusive ppool (api_page_pool conc) ->
    mpool_exclusive ppool' (api_page_pool conc').
  Admitted. (* TODO *)

  Lemma mm_populate_table_pte_reassign
        conc begin parent_table_ptr pte_index level flags ppool :
    let parent_table := ptable_deref conc parent_table_ptr in
    let ret := mm_populate_table_pte conc begin parent_table pte_index level
                                     flags ppool in
    let new_parent_table := fst (fst (fst ret)) in
    let conc' := snd (fst ret) in
    let ppool' := snd ret in
    is_valid conc ->
    locations_exclusive (ptable_deref conc) ppool ->
    is_valid (reassign_pointer conc' parent_table_ptr new_parent_table).
  Admitted. (* TODO *)
  Hint Resolve mm_populate_table_pte_reassign.

  (* the new parent table state returned by mm_populate_table_pte is equivalent
     to the old one in terms of attributes (albeit not structure), so replacing
     the old parent table with the new one produces an equivalent state. *)
  Lemma mm_populate_table_pte_reassign_equiv
        conc begin parent_table_ptr pte_index level flags ppool :
    let parent_table := ptable_deref conc parent_table_ptr in
    let ret := mm_populate_table_pte conc begin parent_table pte_index level
                                     flags ppool in
    let new_parent_table := fst (fst (fst ret)) in
    let conc' := snd (fst ret) in
    let ppool' := snd ret in
    is_valid conc ->
    locations_exclusive (ptable_deref conc) ppool ->
    mpool_fallback ppool = Some conc.(api_page_pool) ->
    mpool_exclusive ppool (api_page_pool conc) ->
    concrete_state_equiv
      (reassign_pointer conc' parent_table_ptr new_parent_table)
      conc.
  Admitted. (* TODO *)

  Lemma mm_populate_table_pte_get_entry
        conc begin parent_table_ptr child_ptr pte_index level flags ppool :
    let parent_table := ptable_deref conc parent_table_ptr in
    let ret := mm_populate_table_pte conc begin parent_table pte_index (S level)
                                     flags ppool in
    let new_parent_table := fst (fst (fst ret)) in
    let maybe_new_child_ptr := snd (fst (fst ret)) in
    let conc' := snd (fst ret) in
    let ppool' := snd ret in
    maybe_new_child_ptr = Some child_ptr ->
    get_entry new_parent_table pte_index = Some (arch_mm_table_pte level child_ptr).
  Admitted. (* TODO *)

  Lemma mm_populate_table_pte_pointer_neq
        conc begin parent_table_ptr child_ptr pte_index level flags ppool :
    let parent_table := ptable_deref conc parent_table_ptr in
    let ret := mm_populate_table_pte conc begin parent_table pte_index level
                                     flags ppool in
    let new_parent_table := fst (fst (fst ret)) in
    let maybe_new_child_ptr := snd (fst (fst ret)) in
    let conc' := snd (fst ret) in
    let ppool' := snd ret in
    is_valid conc ->
    maybe_new_child_ptr = Some child_ptr ->
    locations_exclusive (ptable_deref conc) ppool ->
    parent_table_ptr <> child_ptr.
  Admitted. (* TODO *)

  (* TODO : move *)
  Definition has_location_at_level conc ptr level : Prop :=
    exists idxs root_ptable stage ,
      level_from_indices stage idxs = level
      /\ root_ptable_matches_stage root_ptable stage
      /\ has_location (ptable_deref conc) ptr
                      (table_loc (api_page_pool conc) root_ptable idxs).
  Definition pointers_unchanged_above_level conc1 conc2 level : Prop :=
    forall ptr level',
      has_location_at_level conc1 ptr level' ->
      level < level' ->
      ptable_deref conc2 ptr = ptable_deref conc1 ptr.
  Lemma has_location_at_level_unchanged conc1 conc2 ptr level level' :
    pointers_unchanged_above_level conc1 conc2 level ->
    level <= level' -> (* <= here instead of < because we're not dereferencing *)
    has_location_at_level conc1 ptr level' ->
    has_location_at_level conc2 ptr level'.
  Admitted.

  (* mm_populate_table_pte doesn't alter pointers in the level above *)
  Lemma mm_populate_table_pte_deref_above
        conc begin parent_table_ptr pte_index level flags ppool :
    let parent_table := ptable_deref conc parent_table_ptr in
    let ret := mm_populate_table_pte conc begin parent_table pte_index level
                                     flags ppool in
    let new_parent_table := fst (fst (fst ret)) in
    let maybe_new_child_ptr := snd (fst (fst ret)) in
    let conc' := snd (fst ret) in
    let ppool' := snd ret in
    is_valid conc ->
    has_location_at_level conc parent_table_ptr (S level) ->
    locations_exclusive (ptable_deref conc) ppool ->
    pointers_unchanged_above_level conc conc' (S level).
  Admitted. (* TODO *)

  Lemma mm_populate_table_pte_has_location
        conc begin parent_table_ptr child_ptr pte_index level flags ppool :
    let parent_table := ptable_deref conc parent_table_ptr in
    let ret := mm_populate_table_pte conc begin parent_table pte_index level
                                     flags ppool in
    let new_parent_table := fst (fst (fst ret)) in
    let maybe_new_child_ptr := snd (fst (fst ret)) in
    let conc' := snd (fst ret) in
    let ppool' := snd ret in
    is_valid conc ->
    maybe_new_child_ptr = Some child_ptr ->
    locations_exclusive (ptable_deref conc) ppool ->
    has_location_at_level conc parent_table_ptr (S level) ->
    has_location_at_level (reassign_pointer conc' parent_table_ptr new_parent_table)
                          child_ptr level.
  Admitted. (* TODO *)

  (*** Proofs about [mm_map_level] ***)

  (* TODO : move *)
  Lemma page_attrs'_absent deref t a level stage :
    arch_mm_pte_is_present (nth_default_oobe (entries t) (mm_index a level)) level = false ->
    attrs_present (page_attrs' deref (pa_addr (pa_from_va (va_init a))) t (S level) stage) = false.
  Admitted. (* TODO *)

  (* TODO : move *)
  Lemma attrs_present_absent_attrs : attrs_present absent_attrs = false.
  Proof.
    cbv [attrs_present]; rewrite absent_attrs_invalid.
    cbn [orb]; apply Bool.negb_true_iff.
    rewrite absent_attrs_unowned; reflexivity.
  Qed.

  (* TODO : move *)
  Lemma attrs_equiv_absent attrs stage :
    attrs_present attrs = false -> attrs_equiv attrs absent_attrs stage.
  Proof.
    intros. pose proof attrs_present_absent_attrs.
    cbv [attrs_equiv attrs_present] in *; destruct stage;
      repeat match goal with
             | _ => progress basics
             | _ => inversion_bool
             | |- context [N.eqb ?x ?y] =>
               case_eq (N.eqb x y)
             | _ => solver
             end.
  Qed.

  (* TODO : move *)
  Lemma attrs_changed_in_range_trivial deref idxs table level attrs a stage :
    attrs_changed_in_range deref idxs table table level attrs a a stage.
  Proof.
    cbv [attrs_changed_in_range
           has_uniform_attrs attrs_outside_range_unchanged]; basics; solver.
  Qed.
  Hint Resolve attrs_changed_in_range_trivial.

  Lemma attrs_changed_in_range_level_end
        deref idxs old_table new_table level attrs begin stage :
    attrs_changed_in_range deref idxs old_table new_table (S level) attrs begin
                           (mm_level_end begin level) stage ->
    forall end_,
      (mm_level_end begin level <= end_)%N ->
      attrs_changed_in_range
        deref idxs old_table new_table (S level) attrs begin end_ stage.
  Admitted.

  (* TODO : move *)
  Lemma ptable_deref_reassign_pointer conc ptr t :
    ptable_deref (reassign_pointer conc ptr t)
    = update_deref (ptable_deref conc) ptr t.
  Proof. destruct conc; reflexivity. Qed.
  Lemma api_page_pool_reassign_pointer conc ptr t :
    api_page_pool (reassign_pointer conc ptr t) = api_page_pool conc.
  Proof. destruct conc; reflexivity. Qed.

  (* TODO : move *)
  Hint Resolve mm_entry_size_power_two.
  Hint Resolve absent_not_table block_not_table.
  Hint Rewrite mm_free_page_pte_represents mm_replace_entry_represents : push_concrete.
  Hint Rewrite mm_free_page_pte_fallback mm_replace_entry_fallback
       mm_populate_table_pte_fallback using solver : push_fallback.
  Hint Rewrite ptable_deref_reassign_pointer api_page_pool_reassign_pointer : push_concrete.

  (* dumb wrapper for one of the invariants so it doesn't get split too early *)
  Definition is_begin_or_block_start
             (init_begin begin : ptable_addr_t) level : Prop :=
      (begin = init_begin \/ is_start_of_block begin (mm_entry_size level)).

  (* dumb wrapper for one of the invariants so it doesn't get split too early *)
  Definition end_of_level_or_index_matches
             (init_begin begin : ptable_addr_t) level pte_index : Prop :=
    begin = mm_level_end init_begin level \/ pte_index = mm_index begin level.

  (* Helper definition -- given attrs and flags, returns the expected attributes
     of new PTES (the attributes of an absent PTE if UNMAP is set, and attrs
     otherwise). *)
  Definition new_attrs (attrs : attributes) (flags : int) :=
    if ((flags & MM_FLAG_UNMAP) != 0)%N
    then absent_attrs
    else attrs.

  Definition table_attributes_match deref (t1 t2 : mm_page_table) level stage : Prop :=
    forall a : uintpaddr_t,
      address_wf a stage ->
      attrs_equiv (page_attrs' deref a t1 level stage)
                  (page_attrs' deref a t2 level stage) stage.

  Definition mm_map_level_loop_invariant
        init_abst init_conc init_begin end_capped level attrs flags table_ptr
        (state : concrete_state * ptable_addr_t * paddr_t * size_t * bool * mpool)
    : Prop :=
    let '(conc, begin, pa, pte_index, failed, ppool) := state in
    (* [begin] is either equal to its starting value or is the start
       of a block *)
    (is_begin_or_block_start init_begin begin level
     (* ..and concrete state is valid *)
     /\ is_valid conc
     (* ...and locations are exclusive with the local pool *)
     /\ locations_exclusive (ptable_deref conc) ppool
     (* ...and the backup page pool is the api_page_pool *)
     /\ mpool_fallback ppool = Some (api_page_pool conc)
     (* ...and the local and global pools don't overlap *)
     /\ mpool_exclusive ppool (api_page_pool conc)
     (* ...and [begin] is greater than or equal to the initial value *)
     /\ (init_begin <= begin)%N
     (* ...and either we've reached the end of the level, or the address
        matches the sequence of indices we expect *)
     /\ end_of_level_or_index_matches init_begin begin level pte_index
     (* ...and we don't alter pointers at the level above *)
     /\ pointers_unchanged_above_level init_conc conc (S level)
     (* ...and the concrete state is represented by the correct abstract state *)
     /\ (if ((flags & MM_FLAG_COMMIT) != 0)%N
         then if failed
              then
                (* if COMMIT, but the loop failed, there must be some place in
                   between the initial start address and the current start
                   address where the attribute-changes stopped *)
                (exists end_,
                    (init_begin <= end_ <= N.min begin end_capped)%N
                    /\ represents
                         (abstract_reassign_pointer
                            init_abst init_conc table_ptr
                            (new_attrs attrs flags) init_begin end_)
                         conc)
              else
                (* if COMMIT and !failed, then the attributes have been changed
                   up through the current value of [begin] (or are done through
                   end_capped) *)
                represents
                  (abstract_reassign_pointer
                     init_abst init_conc table_ptr
                     (new_attrs attrs flags) init_begin (N.min begin end_capped))
                  conc
         else
           (* if !COMMIT, abstract state hasn't changed *)
           represents init_abst conc)).

  Definition mm_map_level_loop_arguments_sig
             conc begin end_ pa attrs table_ptr level flags ppool :
    let state := (concrete_state * ptable_addr_t * paddr_t * size_t * bool
                  * mpool)%type in
    { loop_args : nat * (state -> bool) * state * (state -> state * bool)  |
      mm_map_level conc begin end_ pa attrs table_ptr level flags ppool =
      let '(s, _, _,  _, failed, ppool) :=
          @while_loop state (fst (fst (fst loop_args)))
                      (snd (fst (fst loop_args)))
                      (snd (fst loop_args)) (snd loop_args) in
      (negb failed, s, ppool) }.
  Proof.
    destruct level; cbn [mm_map_level];
      match goal with
        |- context [@while_loop _ ?max_iter ?cond ?start ?body] =>
        exists (max_iter, cond, start, body) end;
      reflexivity.
  Defined.
  Definition mm_map_level_loop_arguments :=
    Eval cbv [proj1_sig mm_map_level_loop_arguments_sig] in
      (fun conc begin end_ pa attrs table_ptr level flags ppool =>
         proj1_sig
           (mm_map_level_loop_arguments_sig conc begin end_ pa attrs table_ptr level flags ppool)).
  Lemma mm_map_level_loop_arguments_eq
        conc begin end_ pa attrs table_ptr level flags ppool :
    mm_map_level conc begin end_ pa attrs table_ptr level flags ppool =
    let '(max_iter, cond, start, body) :=
        mm_map_level_loop_arguments
          conc begin end_ pa attrs table_ptr level flags ppool in
    let '(s, _, _, _, failed, ppool) :=
        @while_loop _ max_iter cond start body in
    (negb failed, s, ppool).
  Proof.
    change (mm_map_level_loop_arguments
              conc begin end_ pa attrs table_ptr level flags ppool) with
        (proj1_sig (mm_map_level_loop_arguments_sig
                      conc begin end_ pa attrs table_ptr level flags ppool)).
    pose proof
         (proj2_sig (mm_map_level_loop_arguments_sig
                       conc begin end_ pa attrs table_ptr level flags ppool)) as Hproj2.
    destruct
        (proj1_sig (mm_map_level_loop_arguments_sig
                      conc begin end_ pa attrs table_ptr level flags ppool)) as
        [ [ [ ? ? ] ? ] ? ].
    apply Hproj2.
  Qed.

  (* TODO : move *)
  Lemma reassign_pointer_same conc ptr :
    is_valid conc ->
    concrete_state_equiv
      (reassign_pointer conc ptr (ptable_deref conc ptr)) conc.
  Admitted. (* conceptually easy but a lot of funext threading *)
  Hint Resolve reassign_pointer_same.

  (* TODO : move *)
  Lemma locations_exclusive_ext deref1 deref2 ppool :
    (forall ptr, deref1 ptr = deref2 ptr) ->
    locations_exclusive deref1 ppool <->
    locations_exclusive deref2 ppool.
  Admitted. (* conceptually easy but a lot of funext threading *)

  Lemma locations_exclusive_noop deref ptr ppool:
    locations_exclusive deref ppool ->
    locations_exclusive (update_deref deref ptr (deref ptr)) ppool.
  Proof.
    basics; eapply locations_exclusive_ext; [ basics | solver ].
    cbv [update_deref]; break_match; solver.
  Qed.
  Hint Resolve locations_exclusive_noop.

  (* TODO : move *)
  Lemma update_page_pool_proper conc1 conc2 ppool :
    concrete_state_equiv conc1 conc2 ->
    concrete_state_equiv (update_page_pool conc1 ppool)
                         (update_page_pool conc2 ppool).
  Admitted.

  (* TODO : move *)
  Lemma update_page_pool_valid conc ppool :
    locations_exclusive (ptable_deref conc) ppool ->
    is_valid conc ->
    is_valid (update_page_pool conc ppool).
  Proof. cbv [is_valid]; basics; solver. Qed.

  (* TODO : move *)
  Lemma empty_equiv_replace_absent conc parent_ptr parent child_index child_ptr level :
    parent = ptable_deref conc parent_ptr ->
    get_entry parent child_index = Some (arch_mm_table_pte level child_ptr) ->
    mm_page_table_is_empty (ptable_deref conc child_ptr) level = true ->
    concrete_state_equiv
      (reassign_pointer conc parent_ptr
                        (mm_page_table_replace_entry
                           parent (arch_mm_absent_pte (S level)) child_index))
      conc.
  Admitted.

  (* TODO : might need to accomodate removing the child_ptr from the pool *)
  Lemma locations_exclusive_replace_absent
        conc parent_ptr parent child_index child_ptr level ppool :
    parent = ptable_deref conc parent_ptr ->
    get_entry parent child_index = Some (arch_mm_table_pte level child_ptr) ->
    mm_page_table_is_empty (ptable_deref conc child_ptr) level = true ->
    locations_exclusive (ptable_deref conc) ppool ->
    locations_exclusive
      (update_deref (ptable_deref conc) parent_ptr
                    (mm_page_table_replace_entry
                       parent (arch_mm_absent_pte (S level)) child_index))
      ppool.
  Admitted.

  (* TODO : move *)
  Lemma update_deref_eq deref ptr t :
    update_deref deref ptr t ptr = t.
  Admitted.
  Lemma update_deref_neq deref ptr1 ptr2 t :
    ptr1 <> ptr2 ->
    update_deref deref ptr1 t ptr2 = deref ptr2.
  Admitted.
  Hint Rewrite update_deref_eq update_deref_neq using solver : push_concrete.

  (* TODO : move *)
  Lemma abstract_reassign_pointer_proper abst conc1 conc2 ptr attrs begin end_ :
    concrete_state_equiv conc1 conc2 ->
    abstract_reassign_pointer abst conc1 ptr attrs begin end_
    = abstract_reassign_pointer abst conc2 ptr attrs begin end_.
  Admitted.

  (* TODO : move *)
  Lemma has_location_at_level_exclusive conc ptr1 ptr2 level1 level2 :
    has_location_at_level conc ptr1 level1 ->
    has_location_at_level conc ptr2 level2 ->
    locations_exclusive (ptable_deref conc) (api_page_pool conc) ->
    level1 <> level2 ->
    ptr1 <> ptr2.
  Proof.
    cbv [has_location_at_level level_from_indices]; basics.
    intro. basics. pose proof hafnium_ptable_nodup.
    match goal with H : locations_exclusive _ _, H1 : _, H2 : _ |- _ =>
                    specialize (H _ _ _ H1 H2); invert H end.
    cbv [root_ptable_matches_stage] in *.
    repeat break_match; basics; solver.
  Qed.

  (* TODO : move *)
  Lemma has_location_at_level_reassign conc ptr level t :
    has_location_at_level conc ptr level ->
    has_location_at_level (reassign_pointer conc ptr t) ptr level.
  Proof.
    cbv [has_location_at_level]; basics.
    autorewrite with push_concrete.
    repeat eexists; basics; try solver.
    apply has_location_update_deref; solver.
  Qed.

  Lemma pointers_unchanged_above_level_trans conc1 conc2 conc3 level :
    pointers_unchanged_above_level conc1 conc2 level ->
    pointers_unchanged_above_level conc2 conc3 level ->
    pointers_unchanged_above_level conc1 conc3 level.
  Admitted.

  Lemma pointers_unchanged_above_level_reassign conc1 conc2 ptr level ptr_level t :
    pointers_unchanged_above_level conc1 conc2 level ->
    has_location_at_level conc1 ptr ptr_level ->
    locations_exclusive (ptable_deref conc1) (api_page_pool conc1) ->
    ptr_level <= level ->
    pointers_unchanged_above_level conc1 (reassign_pointer conc2 ptr t) level.
  Proof.
    cbv [pointers_unchanged_above_level]; basics.
    autorewrite with push_concrete. cbv [update_deref].
    break_match; basics; try solver; [ ].
    match goal with
    | H1 : _, H2 : _ |- _ =>
      pose proof (has_location_at_level_exclusive _ _ _ _ _
                                                  H1 H2 ltac:(solver) ltac:(solver))
    end.
    solver.
  Qed.

  Lemma pointers_unchanged_above_level_weaken conc1 conc2 level :
    pointers_unchanged_above_level conc1 conc2 level ->
    pointers_unchanged_above_level conc1 conc2 (S level).
  Proof.
    cbv [pointers_unchanged_above_level]; basics.
    eapply H; solver.
  Qed.

  Lemma mm_map_level_loop_invariant_holds' level flags end_ attrs begin :
    forall abst conc pa table_ptr ppool,
      (begin < end_)%N ->
      represents abst conc ->
      mpool_fallback ppool = Some (api_page_pool conc) ->
      locations_exclusive (ptable_deref conc) ppool ->
      mpool_exclusive ppool (api_page_pool conc) ->
      has_location_at_level conc table_ptr (S level) ->
      let end_capped := N.min (mm_level_end begin level) end_ in
      let cond := (fun '(_, begin, _, _, _, _) => (begin <? end_capped)%N) in
      let successful := (fun '(_, _, _, _, failed, _) => negb failed) in
      let loop_args := mm_map_level_loop_arguments
                         conc begin end_ pa attrs table_ptr level flags ppool in
      is_while_loop_invariant
        (mm_map_level_loop_invariant
           abst conc begin end_capped level attrs flags table_ptr)
        successful (snd (fst (fst loop_args))) (snd loop_args) ->
      forall P : _ -> Prop,
        (forall state,
            (cond state = false \/ negb (snd (fst state)) = false) ->
            mm_map_level_loop_invariant
              abst conc begin end_capped level attrs flags table_ptr state ->
            P (let '(s, _, _, _, failed, ppool) := state in
               (negb failed, s, ppool))) ->
        P (mm_map_level conc begin end_ pa attrs table_ptr level flags ppool).
  Proof.
    cbv zeta; basics.
    rewrite mm_map_level_loop_arguments_eq.
    simplify.
    let P :=
        match goal with
          |- context [@while_loop _ ?max_iter ?cond ?start ?body] =>
          lazymatch goal with
            |- ?G =>
            let x :=
                lazymatch (eval pattern (@while_loop _ max_iter cond start body) in G) with
                  |?f _ => f end in
            x
          end end in
    let end_capped := constr:(N.min (mm_level_end begin level) end_) in
    eapply
      (while_loop_invariant_strong
         (mm_map_level_loop_invariant
            abst conc begin end_capped level attrs flags table_ptr)
         P
         (fun state => let '(_, _, _, _, failed, _) := state in
                       negb failed)
         (fun state => let '(_, begin, _, _, _, _) := state in
                       N.to_nat begin)
         (N.to_nat end_capped)).
    { (* while loop "value" is okay *)
      destruct level; cbn [mm_map_level_loop_arguments];
        cbv [is_while_loop_value]; simplify;
          try match goal with |- N.to_nat _ < N.to_nat _ =>
                              apply N.to_nat_lt_iff end;
          eauto using N.to_nat_ltb, mm_start_of_next_block_lt. }
    { (* while loop "successful" is okay *)
      destruct level; cbn [mm_map_level_loop_arguments];
        cbv [is_while_loop_success];
        repeat simplify_no_break_step;
        repeat match goal with
                 | _ => progress cbn [fst snd negb] in *
                 | _ => congruence
                 | _ => reflexivity
                 | _ => break_match
               end. }
    { (* invariant behaves like an invariant *)
      solver. }
    { (* we have enough fuel *)
      destruct level; cbn [mm_map_level_loop_arguments];
        simplify. }
    { (* invariant holds at start *)
      pose proof (mm_level_end_lt begin level).
      destruct level; cbn [mm_map_level_loop_arguments];
        cbv [mm_map_level_loop_invariant];
        simplify; cbv [is_begin_or_block_start
                         end_of_level_or_index_matches
                         pointers_unchanged_above_level];
          try solver.
      all:eapply represents_proper_abstr;
        try apply abstract_reassign_pointer_trivial; solver. }
    { (* successful is true at start *)
      destruct level; cbn [mm_map_level_loop_arguments];
        simplify_no_break. }
    { (* invariant implies conclusion *)
      basics;
        match goal with
        | Hinv : ?inv ?s, H : context [forall s, _ -> ?inv s -> P _] |- _ =>
          specialize (H s); simplify; apply H
        end; try solver.
        destruct level; cbn [mm_map_level_loop_arguments] in *;
          cbv [mm_map_level_loop_invariant] in *; simplify. }
  Qed.

  Lemma mm_map_level_loop_invariant_is_invariant level :
    forall abst conc begin end_ pa table_ptr attrs ppool flags,
      (begin < end_)%N ->
      represents abst conc ->
      has_location_at_level conc table_ptr (S level) ->
      let end_capped := N.min (mm_level_end begin level) end_ in
      let successful := (fun '(_, _,  _, _, failed, _) => negb failed) in
      let loop_args := mm_map_level_loop_arguments
                         conc begin end_ pa attrs table_ptr level flags ppool in
      is_while_loop_invariant
        (mm_map_level_loop_invariant
          abst conc begin end_capped level attrs flags table_ptr)
        successful (snd (fst (fst loop_args))) (snd loop_args).
  Proof.
    induction level; cbn [mm_map_level_loop_arguments];
      intros; assert (is_valid conc) by solver.
    { (* level = 0 *)
      simplify_no_break.
      cbv [is_while_loop_invariant]; simplify_no_break; [ solve [simplify] | ].
      Time
      cbv [mm_map_level_loop_invariant] in *; basics;
        (* some [pose proof] statements about the current [begin] address, to
             help [solver] with arithmetic goals *)
        match goal with
        | H : is_begin_or_block_start _ ?b ?level |- _ =>
          pose proof (mm_start_of_next_block_le_level_end b level);
            pose proof (mm_start_of_next_block_lt b (mm_entry_size level) ltac:(solver))
        end;
        (* can't use invert_is_valid because there are two is_valid hypotheses *)
        match goal with
          | H1 : is_valid _, H2 : is_valid _ |- _ =>
            pose proof H1; pose proof H2;
            invert H1; invert H2
        end;
        repeat match goal with
               | _ => progress basics
               (* destruct end_of_level_or_index_matches and eliminate end-of-level
                  case (since it happens at the very end of the loop, it couldn't
                  have happened in the previous loop run) *)
               | H : context [end_of_level_or_index_matches] |- _ =>
                 cbv [end_of_level_or_index_matches] in H;
                   basics; [ repeat inversion_bool; solver | ]
               (* solve the is_valid clause *)
               | |- is_valid _ => eapply concrete_equiv_valid;
                                    solve [eauto using mm_populate_table_pte_equiv]
               (* solve the concrete_state_equiv clause *)
               | |- concrete_state_equiv _ _ =>
                 eapply concrete_state_equiv_trans; [ eassumption | ];
                   solve [eauto using mm_populate_table_pte_equiv]
               (* solve the mpool_exclusive clause *)
               | |- mpool_exclusive _ _ =>
                 solve [eauto using mm_replace_entry_mpool_exclusive,
                        mm_populate_table_pte_mpool_exclusive]
               (* solve the is_begin_or_block_start clause *)
               | |- is_begin_or_block_start _ (mm_start_of_next_block _ _) _ =>
                 cbv [is_begin_or_block_start];
                   solve [auto using mm_start_of_next_block_is_start]
               (* solve the init_begin <= begin clause *)
               | |- (_ <= mm_start_of_next_block ?a ?sz)%N =>
                 pose proof (mm_start_of_next_block_lt a sz ltac:(solver)); solver
               (* solve the pointers_unchanged_above_level clause *)
               | |- pointers_unchanged_above_level _ _ _ =>
                 cbv [pointers_unchanged_above_level]; basics;
                   autorewrite with push_concrete;
                   rewrite update_deref_neq; [ solver | ];
                     eapply has_location_at_level_exclusive; solver
               (* solve the pointers_unchanged_above_level clause *)
               | |- pointers_unchanged_above_level _ _ _ =>
                 cbv [pointers_unchanged_above_level]; basics;
                   autorewrite with push_concrete;
                   rewrite update_deref_neq by (eapply has_location_at_level_exclusive; solver);
                   rewrite mm_populate_table_pte_deref_above; try solver;
                     eapply has_location_at_level_unchanged; solver
               (* solve the end_of_level_or_index_matches clause *)
               | |- context [end_of_level_or_index_matches _ ?x ?l (mm_index ?x ?l)] =>
                 cbv [end_of_level_or_index_matches]; right; solver
               (* solve the end_of_level_or_index_matches clause *)
               | |- context [end_of_level_or_index_matches _ (mm_start_of_next_block ?x _)] =>
                 cbv [end_of_level_or_index_matches];
                   rewrite <-mm_level_end_eq2 with (b:=x) by (repeat inversion_bool; try solver);
                   match goal with
                   | |- ?a = ?b \/ _ => destruct (N.eq_dec a b); [ left; solver | right]
                   end; rewrite mm_index_start_of_next_block; solver
               | _ => rewrite mm_replace_entry_fallback by solver
               | _ => rewrite mm_populate_table_pte_fallback by solver
               | |- locations_exclusive _ _ => eapply mm_replace_entry_exclusive; solver
               | |- locations_exclusive _ _ => eapply mm_populate_table_pte_exclusive; solver
               | |- represents _ _ => eapply mm_populate_table_pte_represents; solver
               | _ => progress autorewrite with push_concrete
               | |- exists _, _ =>
                 solve [eexists; basics;
                          [ | | eapply represents_proper;
                                [ apply concrete_state_equiv_sym,
                                  mm_populate_table_pte_reassign_equiv | ];
                                solver ]; repeat inversion_bool; solver]
               | |- exists _, _ =>
                 solve [ eexists; basics; [ | | solver]; repeat inversion_bool; solver]
               | |- represents _ _ =>
                 solve
                     [eapply represents_proper;
                        [ apply concrete_state_equiv_sym,
                          mm_populate_table_pte_reassign_equiv | ]; solver ]
               | |- represents _ _ =>
                 solve
                     [eapply represents_proper;
                        [ apply concrete_state_equiv_sym,
                          reassign_pointer_same | ]; solver ]
               | _ => simplify_step
               end.
      { (* absent but UNMAP *)
        admit. (* TODO *) }
      { (* present but has the right attributes *)
        admit. (* TODO *) }
      { (* entire entry is in range and UNMAP -- just replace it with an empty PTE *)
        admit. (* TODO *) }
      { (* entire entry is in range and !UNMAP -- just replace it with new PTE *)
        admit. (* TODO *) } }
    { (* level > 0 *)
      simplify_no_break.
      cbv [is_while_loop_invariant]; simplify_no_break; [ solve [simplify] | ].

      (* extract information from the loop invariant *)
      match goal with
      | H : mm_map_level_loop_invariant _ _ _ _ _ _ _ _ _ |- _ =>
        pose proof H; cbv [mm_map_level_loop_invariant] in H;
          repeat match goal with
                 | H : _ /\ _ |- _ => destruct H
                 end
      end.

      (* can't use invert_is_valid because there are two is_valid hypotheses *)
      match goal with
      | H1 : is_valid _, H2 : is_valid _ |- _ =>
        pose proof H1; pose proof H2;
          invert H1; invert H2
      end; basics_no_break.

      (* destruct end_of_level_or_index_matches and eliminate end-of-level case *)
      match goal with
      | H : context [end_of_level_or_index_matches] |- _ =>
        destruct H; [ repeat inversion_bool; subst; solver | ]
      end.

      (* use the inductive hypothesis to state that we can use the invariant for proofs about recursive calls *)
      let end_capped := constr:(N.min (mm_level_end begin (S level)) end_) in 
      match goal with
      | H : mm_map_level_loop_invariant _ _ _ _ _ ?attrs ?flags ?table_ptr
                                        (?c, ?begin, ?pa, ?pte_index, _, ?ppool) |- _ =>
        let Hinv' := fresh in
        let Hinv := fresh in
        pose proof
             (fun conc ppool abst table_ptr =>
                mm_map_level_loop_invariant_holds'
                  level flags end_capped attrs begin abst conc pa table_ptr ppool
                  (ltac:(repeat inversion_bool; solver))
             ) as Hinv';
          pose proof
               (fun conc ppool abst table_ptr
                    Hrep Hfallback Hexcl Hmexcl Hloc =>
                  Hinv' conc ppool abst table_ptr
                        Hrep Hfallback Hexcl Hmexcl Hloc
                        (ltac:(apply IHlevel; repeat inversion_bool; solver))
               )
          as Hinv; clear IHlevel;
            (* specialize the invariant to the concrete state and page pool used in the recursive call *)
            let rec_c := lazymatch goal with |- context [mm_map_level ?x] => constr:(x) end in
            let rec_p := lazymatch goal with |- context [mm_map_level _ _ _ _ _ _ _ _ ?x] => constr:(x) end in
            specialize (Hinv rec_c rec_p); autorewrite with push_concrete in Hinv;
                pose proof (fun abst table_ptr (Hrep:represents abst _) =>
                              Hinv abst table_ptr
                                   Hrep
                                   (ltac:(eauto using mm_populate_table_pte_fallback))
                                   (ltac:(eauto using mm_populate_table_pte_exclusive))
                                   (ltac:(eauto using mm_populate_table_pte_mpool_exclusive))
                           )
                as Hinvariant'; clear Hinv; clear Hinv'
      end.

      (* find the mm_populate_table_pte result and specialize the invariant to
         the new-table argument it returns *)
      match goal with
        |- context [mm_map_level (reassign_pointer
                                    (snd (fst ?x)) ?ptr (fst (fst (fst ?x))))] =>
        assert (forall p, snd (fst (fst x)) = Some p ->
                          has_location_at_level
                            (reassign_pointer (snd (fst x)) ptr (fst (fst (fst x))))
                            p (S level)) as Hloc
            by (basics; apply mm_populate_table_pte_has_location;
                try eapply has_location_at_level_unchanged; solver);
          match goal with
            H :  if _ then _ else represents _ ?c |- _ =>
            assert (forall abst, represents abst c ->
                                 represents abst
                                            (reassign_pointer
                                               (snd (fst x)) ptr (fst (fst (fst x)))))
                   as Hrep
              by (basics; eapply represents_proper;
                  [ eapply concrete_state_equiv_sym; apply mm_populate_table_pte_reassign_equiv; solver | solver ])
          end
      end.
      pose proof (fun abst table_ptr Hrep' Hloc' =>
                    Hinvariant' abst table_ptr (Hrep _ Hrep') (Hloc _ Hloc')) as Hinvariant;
        clear Hinvariant'; clear Hrep; clear Hloc.

      let x := lazymatch goal with |- context [mm_map_level ?x] => constr:(x) end in
      assert (has_location_at_level x table_ptr (S (S level)))
        by (eapply has_location_at_level_reassign; try solver; [ ];
            eapply has_location_at_level_unchanged; try solver; [ ];
            cbv [pointers_unchanged_above_level]; basics;
            rewrite mm_populate_table_pte_deref_above; try solver;
            eapply has_location_at_level_unchanged; solver).

      (* some [pose proof] statements about the current [begin] address, to
         help [solver] with arithmetic goals *)
      match goal with
      | H : is_begin_or_block_start _ ?b ?lvl |- _ =>
        pose proof (mm_start_of_next_block_le_level_end b lvl);
          pose proof (mm_level_end_le_mono_r b level lvl ltac:(solver));
          pose proof (mm_start_of_next_block_lt b (mm_entry_size lvl) ltac:(solver))
      end.

      replace (S level - 1) with level in * by solver.

      Time
        cbv [mm_map_level_loop_invariant]; simplify_no_break;
        (* solve all the easy/bookkeeping clauses of the invariant immediately *)
        try lazymatch goal with
            | |- (begin <= _)%N => solve [simplify]
            | |- is_begin_or_block_start _ _ _ =>
              repeat break_match; cbn [fst snd]; cbv [is_begin_or_block_start];
                auto using mm_start_of_next_block_is_start
            | |- end_of_level_or_index_matches _ _ _ _ =>
              simplify;
                match goal with
                | |- end_of_level_or_index_matches _ ?x ?l (mm_index ?x ?l) =>
                  cbv [end_of_level_or_index_matches]; right; solver
                | |- context [end_of_level_or_index_matches _ (mm_start_of_next_block ?x _)] =>
                  cbv [end_of_level_or_index_matches];
                    rewrite <-mm_level_end_eq2 with (b:=x) by (repeat inversion_bool; try solver);
                    match goal with
                    | |- ?a = ?b \/ _ => destruct (N.eq_dec a b); [ left; solver | right]
                    end; rewrite mm_index_start_of_next_block; solver
                end
            end.
      { (* is_valid clause *)

        (* this subproof doesn't need the detailed case analysis on the abstract
           state; to prevent getting tons of subgoals, we simply prove that *some*
           abstract state represents c and then remove the more detailed
           hypothesis *)
        match goal with
        | H : if _ then _ else represents _ ?c |- _ =>
          assert (exists abst, represents abst c) as Hrep
            by (destruct abst; simplify; eexists; basics; solver);
            clear H; destruct Hrep as [? Hrep]
        end.

        pose proof (fun table Hloc =>
                      Hinvariant _ table Hrep Hloc
                                 (fun ret => is_valid (snd (fst ret)))
                                 (ltac:(cbv [mm_map_level_loop_invariant]; simplify))) as Hvalid.
        pose proof (fun table Hloc =>
                      Hinvariant _ table Hrep Hloc
                                 (fun ret => pointers_unchanged_above_level _ (snd (fst ret)) level)
                                 (ltac:(cbv [mm_map_level_loop_invariant]; simplify))) as Hptrs.
        clear Hinvariant;
          simplify; autorewrite with push_concrete;
            try solve [eauto using mm_populate_table_pte_equiv];
            first [ apply Hvalid
                  | eapply is_valid_proper; [ | apply Hvalid] ];
            try solver; eauto using mm_populate_table_pte_has_location,
                        has_location_at_level_unchanged; [ | ].
        all:eapply empty_equiv_replace_absent;
          try (apply mm_populate_table_pte_get_entry; solver);
          [ | repeat inversion_bool; basics; solver ].
        all:rewrite Hptrs; autorewrite with push_concrete; try solver;
          eauto using mm_populate_table_pte_has_location, has_location_at_level_unchanged. }
      { (* locations_exclusive clause *)

        (* this subproof doesn't need the detailed case analysis on the abstract
           state; to prevent getting tons of subgoals, we simply prove that *some*
           abstract state represents c and then remove the more detailed
           hypothesis *)
        match goal with
        | H : if _ then _ else represents _ ?c |- _ =>
          assert (exists abst, represents abst c) as Hrep
            by (destruct abst; simplify; eexists; basics; solver);
            clear H; destruct Hrep as [? Hrep]
        end.

        pose proof (fun table Hloc =>
                      Hinvariant _ table Hrep Hloc
                                 (fun ret => locations_exclusive (ptable_deref (snd (fst ret))) (snd ret))
                                 (ltac:(cbv [mm_map_level_loop_invariant]; simplify))) as Hexcl.
        pose proof (fun table Hloc =>
                      Hinvariant _ table Hrep Hloc
                                 (fun ret => pointers_unchanged_above_level _ (snd (fst ret)) level)
                                 (ltac:(cbv [mm_map_level_loop_invariant]; simplify))) as Hptrs.
        clear Hinvariant;
          simplify; autorewrite with push_concrete;
            try (apply Hexcl; try solver; apply mm_populate_table_pte_has_location; try solver;
                 eapply has_location_at_level_unchanged; solver);
            try solve [eauto using mm_replace_entry_exclusive,
                       mm_free_page_pte_exclusive, mm_populate_table_pte_exclusive].
        all:apply mm_free_page_pte_exclusive; [ | solver .. ].
        all:eapply locations_exclusive_replace_absent;
          try (apply mm_populate_table_pte_get_entry; solver);
          try (apply Hexcl; try solver; apply mm_populate_table_pte_has_location; try solver;
               eapply has_location_at_level_unchanged; solver);
          [ | repeat inversion_bool; basics; solver ].
        all:rewrite Hptrs; autorewrite with push_concrete; try solver;
          eauto using mm_populate_table_pte_has_location, has_location_at_level_unchanged. }
      { (* mpool_fallback clause *)

        (* this subproof doesn't need the detailed case analysis on the abstract
           state; to prevent getting tons of subgoals, we simply prove that *some*
           abstract state represents c and then remove the more detailed
           hypothesis *)
        match goal with
        | H : if _ then _ else represents _ ?c |- _ =>
          assert (exists abst, represents abst c) as Hrep
            by (destruct abst; simplify; eexists; basics; solver);
            clear H; destruct Hrep as [? Hrep]
        end.

        pose proof (fun table Hloc =>
                      Hinvariant _ table Hrep Hloc
                                       (fun ret => mpool_fallback (snd ret) = Some (api_page_pool (snd (fst ret))))
                                       (ltac:(cbv [mm_map_level_loop_invariant]; simplify)));
                clear Hinvariant;
                simplify; autorewrite with push_concrete push_fallback;
                  solve [eauto using mm_populate_table_pte_represents]. }
      { (* mpool_exclusive clause *)

        (* this subproof doesn't need the detailed case analysis on the abstract
           state; to prevent getting tons of subgoals, we simply prove that *some*
           abstract state represents c and then remove the more detailed
           hypothesis *)
        match goal with
        | H : if _ then _ else represents _ ?c |- _ =>
          assert (exists abst, represents abst c) as Hrep
            by (destruct abst; simplify; eexists; basics; solver);
            clear H; destruct Hrep as [? Hrep]
        end.

        pose proof (fun table Hloc =>
                      Hinvariant _ table Hrep Hloc
                                 (fun ret => mpool_exclusive (snd ret) (api_page_pool (snd (fst ret))))
                                 (ltac:(cbv [mm_map_level_loop_invariant]; simplify))).
        pose proof (fun table Hloc =>
                      Hinvariant _ table Hrep Hloc
                                 (fun ret => pointers_unchanged_above_level _ (snd (fst ret)) level)
                                 (ltac:(cbv [mm_map_level_loop_invariant]; simplify))) as Hptrs.
        pose proof (fun table Hloc =>
                      Hinvariant _ table Hrep Hloc
                                 (fun ret => locations_exclusive (ptable_deref (snd (fst ret)))
                                                                 (api_page_pool (snd (fst ret))))
                                 (ltac:(cbv [mm_map_level_loop_invariant is_valid]; simplify))) as Hexcl;
          clear Hinvariant;
          simplify; autorewrite with push_concrete;
            try solve [eauto using mm_replace_entry_mpool_exclusive,
                       mm_free_page_pte_mpool_exclusive, mm_populate_table_pte_mpool_exclusive].
        all:apply mm_free_page_pte_mpool_exclusive; [ | solver .. ];
          autorewrite with push_concrete.
        all:eapply locations_exclusive_replace_absent;
          try (apply mm_populate_table_pte_get_entry; solver);
          try (apply Hexcl; try solver; apply mm_populate_table_pte_has_location; try solver;
               eapply has_location_at_level_unchanged; solver);
          [ | repeat inversion_bool; basics; solver ].
        all:rewrite Hptrs; autorewrite with push_concrete; try solver;
          eauto using mm_populate_table_pte_has_location, has_location_at_level_unchanged. }
      { (* pointers_unchanged_above_level clause *)

        (* this subproof doesn't need the detailed case analysis on the abstract
           state; to prevent getting tons of subgoals, we simply prove that *some*
           abstract state represents c and then remove the more detailed
           hypothesis *)
        match goal with
        | H : if _ then _ else represents _ ?c |- _ =>
          assert (exists abst, represents abst c) as Hrep
            by (destruct abst; simplify; eexists; basics; solver);
            clear H; destruct Hrep as [? Hrep]
        end.

        pose proof (fun table Hloc =>
                      Hinvariant _ table Hrep Hloc
                                 (fun ret => pointers_unchanged_above_level _ (snd (fst ret)) level)
                                 (ltac:(cbv [mm_map_level_loop_invariant]; simplify))) as Hptrs.
        clear Hinvariant;
          simplify; autorewrite with push_concrete;
            try (eapply pointers_unchanged_above_level_reassign; solver);
            repeat match goal with
                   | _ => eapply pointers_unchanged_above_level_reassign; try solver; [ ]
                   | _ => eapply pointers_unchanged_above_level_trans;
                            [ | apply pointers_unchanged_above_level_weaken, Hptrs; solver ]
                   | _ => eapply pointers_unchanged_above_level_trans;
                            [ | apply mm_populate_table_pte_deref_above;
                                try solver; eapply has_location_at_level_unchanged; solver ]
                   | _ => solver
                   end. }
      { (* represents clause *)

        Local Ltac specialize_invariant :=
          cbv [mm_map_level_loop_invariant]; simplify; try (repeat inversion_bool; solver);
          erewrite abstract_reassign_pointer_proper with (conc1:=reassign_pointer _ _ _) in *
            by (eapply mm_populate_table_pte_reassign_equiv; solver);
          try match goal with
              | H : true = true -> _ |- _ => specialize (H ltac:(solver))
              end;
          try match goal with
              | H : represents (?F ?x) ?c |- exists ec, represents (?F (N.min ec _)) ?c =>
                exists x; basics; rewrite ?(N.min_l x) by solver; try solver
              | _ =>  do 2 eexists; basics; [ | | solver]; try solver;
                      repeat inversion_bool; rewrite N.min_r by solver;
                      apply N.min_case; try eapply mm_level_end_le; solver
              end.

          repeat inversion_bool.
          let Hx:= fresh in
          let Hi := fresh in
          match type of Hinvariant with
            forall _ y, _ -> ?x = Some y -> _ =>
            case_eq x;
              [ intros new_table Hx;
                pose proof (fun abst Hrep => Hinvariant abst _ Hrep Hx) as Hi;
                clear Hinvariant; pose proof Hi as Hinvariant; clear Hi
              | (* clear the invariant in the second case, since nothing fits its
                   preconditions (and we shouldn't do recursive calls in this case) *)
              clear Hinvariant ] end.
          { (* case where we *do* need the invariant -- specialize it *)
            let new_begin :=
                match goal with H : is_begin_or_block_start _ ?x (S level) |- _ =>
                                constr:(x) end in
            let P :=
                match goal with
                | H : if _ then if ?failed then _ else _ else represents ?init_abst ?c |- _ =>
                  let e := match type of H with ?P => P end in
                  let F := lazymatch (eval pattern failed in e) with
                           | ?f _ => f end in
                  let F := lazymatch (eval pattern c in F) with
                           | ?f _ => f end in
                  let F := lazymatch (eval pattern new_begin in F) with
                           | ?f _ => f end in
                  let F := lazymatch (eval pattern begin in F) with
                           | ?f _ => f end in
                  let F := lazymatch (eval pattern table_ptr in F) with
                           | ?f _ => f end in
                  let F := lazymatch (eval pattern conc in F) with
                           | ?f _ => f end in
                  let F := lazymatch (eval pattern init_abst in F) with
                           | ?f _ => f end in
                  constr:(F)
                end in
              let Hx := fresh in
              let Hf := fresh in
              match goal with
              | H : if ?x then if ?failed then _ else _ else represents ?init_abst ?c |- _ =>
                case_eq x; intro Hx;
                  case_eq failed; intro Hf;
                    rewrite !Hx in *;
                    rewrite !Hf in *
              end;
                repeat match goal with
                       | H : exists _, _ |- _ => destruct H
                       | H : _ /\ _ |- _ => destruct H
                       end;
                let x_expr := match type of Hx with ?e = _ => e end in
                let x_value := match type of Hx with _ = ?e => e end in
                let failed_expr := match type of Hf with ?b = _ => b end in 
                let failed_value := match type of Hf with _ = ?b => b end in
                match goal with
                | H : represents ?a c |- _ =>
                  specialize (Hinvariant a H
                                         (fun ret =>
                                            x_expr = x_value ->
                                            (failed_value = true -> (fst (fst ret)) = false) ->
                                            exists end_capped,
                                              P a c new_table new_begin end_capped (snd (fst ret)) (fst (fst ret))))
                end;
                  match type of Hinvariant with ?P -> _ =>
                                                let H2 := fresh in
                                                assert P as H2 by specialize_invariant;
                                                  specialize (Hinvariant H2)
                  end;
                  try match goal with
                      | H : true = false |- _ => congruence
                      | H : false = true |- _ => congruence
                      end.
            (* now we can use the invariant on the recursive call *)
            (* 2 subgoals represent the 2 possible values of COMMIT *)
            1-2:admit. }
          { (* includes only non-recursive cases *)
            repeat inversion_bool; basics; [ ].
            admit. }
      Unshelve.
          all:solver.
  Admitted.

  Lemma mm_map_level_loop_invariant_holds level flags end_ attrs begin :
    forall abst conc pa table ppool,
      (begin < end_)%N ->
      represents abst conc ->
      mpool_fallback ppool = Some (api_page_pool conc) ->
      locations_exclusive (ptable_deref conc) ppool ->
      mpool_exclusive ppool (api_page_pool conc) ->
      has_location_at_level conc table (S level) ->
      let end_capped := N.min (mm_level_end begin level) end_ in
      let cond := (fun '(_, begin, _, _, _, _) => (begin <? end_capped)%N) in
      forall P : _ -> Prop,
        (forall state,
            (cond state = false \/ negb (snd (fst state)) = false) ->
            mm_map_level_loop_invariant
              abst conc begin end_capped level attrs flags table state ->
            P (let '(s, _, _, _, failed, ppool) := state in
               (negb failed, s, ppool))) ->
        P (mm_map_level conc begin end_ pa attrs table level flags ppool).
  Proof.
    cbv zeta; basics.
    eapply mm_map_level_loop_invariant_holds'; eauto; [ ].
    apply mm_map_level_loop_invariant_is_invariant; eauto.
  Qed.

  (* case where mm_map_level succeeds and COMMIT = true *)
  Lemma mm_map_level_represents_commit abst (conc : concrete_state) level :
    forall begin end_ pa attrs table_ptr flags ppool,
      (begin < end_)%N ->
      mpool_fallback ppool = Some (api_page_pool conc) ->
      locations_exclusive (ptable_deref conc) ppool ->
      mpool_exclusive ppool (api_page_pool conc) ->
      has_location_at_level conc table_ptr level ->
      ((flags & MM_FLAG_COMMIT) != 0)%N = true ->
      let end_capped := N.min (mm_level_end begin level) end_ in
      let ret := mm_map_level
                   conc begin end_ pa attrs table_ptr level flags ppool in
      let success := fst (fst ret) in
      let conc' := snd (fst ret) in
      success = true ->
      represents abst conc ->
      represents
        (abstract_reassign_pointer
           abst conc table_ptr (new_attrs attrs flags) begin end_capped)
        conc'.
  Proof.
    cbv zeta; basics.
    repeat match goal with H : context [mm_map_level] |- _ => revert H end.
    eapply mm_map_level_loop_invariant_holds; eauto; [ ].
    cbv [mm_map_level_loop_invariant]; simplify;
      repeat inversion_bool; rewrite ?N.min_r in * by solver;
        solver.
  Qed.

  Lemma mm_map_level_locations_exclusive :
    forall level flags end_ attrs begin abst conc pa table ppool,
      (begin < end_)%N ->
      represents abst conc ->
      mpool_fallback ppool = Some (api_page_pool conc) ->
      locations_exclusive (ptable_deref conc) ppool ->
      mpool_exclusive ppool (api_page_pool conc) ->
      has_location_at_level conc table level ->
      let ret :=
          mm_map_level conc begin end_ pa attrs table level flags ppool in
      let conc' := snd (fst ret) in
      let ppool' := snd ret in
      locations_exclusive (ptable_deref conc') ppool'.
  Proof.
    cbv zeta; basics.
    repeat match goal with H : context [mm_map_level] |- _ => revert H end.
    eapply mm_map_level_loop_invariant_holds; eauto; [ ].
    cbv [mm_map_level_loop_invariant]; simplify.
  Qed.

  Lemma mm_map_level_locations_mpool_exclusive :
    forall level flags end_ attrs begin abst conc pa table ppool,
      (begin < end_)%N ->
      represents abst conc ->
      mpool_fallback ppool = Some (api_page_pool conc) ->
      locations_exclusive (ptable_deref conc) ppool ->
      mpool_exclusive ppool (api_page_pool conc) ->
      has_location_at_level conc table level ->
      let ret :=
          mm_map_level conc begin end_ pa attrs table level flags ppool in
      let conc' := snd (fst ret) in
      let ppool' := snd ret in
      mpool_exclusive ppool' (api_page_pool conc').
  Proof.
    cbv zeta; basics.
    repeat match goal with H : context [mm_map_level] |- _ => revert H end.
    eapply mm_map_level_loop_invariant_holds; eauto; [ ].
    cbv [mm_map_level_loop_invariant]; simplify.
  Qed.

  Lemma mm_map_level_fallback level :
    forall abst conc begin end_ pa attrs table_ptr flags ppool,
      (begin < end_)%N ->
      represents abst conc ->
      mpool_fallback ppool = Some (api_page_pool conc) ->
      locations_exclusive (ptable_deref conc) ppool ->
      mpool_exclusive ppool (api_page_pool conc) ->
      has_location_at_level conc table_ptr level ->
      let ret :=
          mm_map_level conc begin end_ pa attrs table_ptr level flags ppool in
      let conc' := snd (fst ret) in
      let ppool' := snd ret in
      mpool_fallback ppool = Some (api_page_pool conc) ->
      mpool_fallback ppool' = Some (api_page_pool conc').
  Proof.
    cbv zeta; basics.
    repeat match goal with H : context [mm_map_level] |- _ => revert H end.
    eapply mm_map_level_loop_invariant_holds; eauto; [ ].
    cbv [mm_map_level_loop_invariant]; simplify.
  Qed.

  (*** Helpers for [mm_map_root] proofs ***)

  (* TODO : move *)
  (* if a pointer is in the root list, and the root page table is well-formed,
     then there is exactly one index sequence and it has length 1 *)
  Lemma index_sequences_to_root deref ptr root_ptable stage i :
    root_ptable_matches_stage root_ptable stage ->
    root_ptable_wf deref stage root_ptable ->
    nth_error (mm_page_table_from_pa (root root_ptable)) i = Some ptr ->
    index_sequences_to_pointer
      deref ptr root_ptable stage = cons (cons i nil) nil.
  Admitted. (* TODO *)

  (* TODO : move *)
  Lemma NoDup_nth_error_neq {A} (l : list A) i j x y :
    NoDup l ->
    nth_error l i = Some x ->
    nth_error l j = Some y ->
    i <> j ->
    x <> y.
  Admitted.

  (* TODO : move *)
  Lemma index_sequences_wrong_ptable deref ptr ppool root_ptable idxs stage :
    has_location deref ptr (table_loc ppool root_ptable idxs) ->
    forall root_ptable2,
      root_ptable <> root_ptable2 ->
      root_ptable_matches_stage root_ptable2 stage ->
      index_sequences_to_pointer deref ptr root_ptable2 stage = nil.
  Admitted.

  (* TODO : move *)
  Lemma is_valid_root_wf c root_ptable stage :
    is_valid c ->
    root_ptable_matches_stage root_ptable stage ->
    root_ptable_wf (ptable_deref c) stage root_ptable.
  Admitted. (* easy *)
  Hint Resolve is_valid_root_wf.

  (* TODO : move *)
  (* this is basically another version of has_location_nth_default *)
  Lemma root_pointer_has_location deref root_ptable root_ptr ppool i :
    nth_error (mm_page_table_from_pa (root root_ptable)) i = Some root_ptr ->
    has_location deref root_ptr (table_loc ppool root_ptable (cons i nil)).
  Admitted.

  (* TODO : move *)
  Lemma root_ptable_matches_stage_In root_ptable stage :
    root_ptable_matches_stage root_ptable stage ->
    In root_ptable all_root_ptables.
  Proof.
    destruct stage;
      cbv [root_ptable_matches_stage all_root_ptables]; basics; solver.
  Qed.

  (* TODO : move *)
  Lemma nth_error_eq_default {A} (l : list A) i d :
    i < length l ->
    nth_error l i = Some (nth_default d l i).
  Admitted. (* easy *)

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

  (* TODO : move *)
  Lemma has_location_at_level_nth_default conc root_ptable i flags root_level :
    ptable_is_root root_ptable flags ->
    is_root root_level flags ->
    i < length (mm_page_table_from_pa (root (root_ptable))) ->
    has_location_at_level conc
                          (nth_default_oobe (mm_page_table_from_pa (root root_ptable)) i)
                          root_level.
  Proof.
    cbv [has_location_at_level]; basics; repeat eexists;
      try eapply has_location_nth_default; try solver; [ ].
    cbv [level_from_indices is_root mm_max_level stage_from_flags max_level] in *.
    simplify; autorewrite with push_length; solver.
  Qed.

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

  Definition represents_clause init_abst init_conc t_ptrs init_begin end_ attrs flags
             table_index (failed : bool) conc :=
    (if ((flags & MM_FLAG_COMMIT) != 0)%N
          then if failed
               then
                 (* if COMMIT and failed, our concrete state is represented by
                    the abstract state that corresponds to processing the first
                    [table_index] entries of the original list, but with a
                    different end address *)
                 (exists mid,
                     (init_begin <= mid <= end_)%N
                     /\ (represents
                           (fold_left
                              (fun abst t_ptr =>
                                 abstract_reassign_pointer
                                   abst init_conc t_ptr (new_attrs attrs flags)
                                   init_begin mid)
                              (firstn table_index t_ptrs)
                              init_abst) conc))
               else
                 (* if COMMIT and !failed, our concrete state is represented by
                    the abstract state that  corresponds to processing the first
                    [table_index] entries of the original list *)
                 (represents
                       (fold_left
                          (fun abst t_ptr =>
                             abstract_reassign_pointer
                               abst init_conc t_ptr (new_attrs attrs flags)
                               init_begin end_)
                          (firstn table_index t_ptrs)
                          init_abst) conc)
          else
            (* if !COMMIT, the abstract state hasn't changed *)
            represents init_abst conc).

  Definition mm_map_root_loop_invariant
             init_abst init_conc t_ptrs init_begin end_ attrs flags root_level
             (state : concrete_state * ptable_addr_t * size_t * bool * mpool)
    : Prop :=
    let '(conc, begin, table_index, failed, ppool) := state in
     (* table_index stays in sync with [begin] *)
     (table_index = table_index_expression begin end_ root_level
      (* ...and [begin] increases monotonically *)
      /\ (init_begin <= begin)%N
      (* ..and [begin] is either equal to its starting value or is the start
         of a block *)
      /\ is_begin_or_block_start init_begin begin root_level
      (* ...and the page tables and local page pool don't overlap *)
      /\ locations_exclusive (ptable_deref conc) ppool
      (* ...and the fallback of the local page pool is the global one *)
      /\ mpool_fallback ppool = Some (api_page_pool conc)
      (* ...and local and global pools don't overlap *)
      /\ mpool_exclusive ppool (api_page_pool conc)
                         (*
      (* ...and we don't add/remove/change references to the root page tables  *)
      /\ (Forall (fun t_ptr =>
                    forall root_ptable stage,
                      root_ptable_matches_stage root_ptable stage ->
                      index_sequences_to_pointer
                        (ptable_deref init_conc) t_ptr root_ptable stage
                      = index_sequences_to_pointer
                          (ptable_deref s) t_ptr root_ptable stage)
                 t_ptrs) *)
      (* ...and the concrete state is represented by the abstract state we
         expect based on COMMIT and failed *)
      /\ (if ((flags & MM_FLAG_COMMIT) != 0)%N
          then if failed
               then
                 (* if COMMIT and failed, our concrete state is represented by
                    the abstract state that corresponds to processing the first
                    [table_index] entries of the original list, but with a
                    different end address *)
                 (exists mid,
                     (init_begin <= mid <= end_)%N
                     /\ (represents
                           (fold_left
                              (fun abst t_ptr =>
                                 abstract_reassign_pointer
                                   abst init_conc t_ptr (new_attrs attrs flags)
                                   init_begin mid)
                              (firstn table_index t_ptrs)
                              init_abst) conc))
               else
                 (* if COMMIT and !failed, our concrete state is represented by
                    the abstract state that  corresponds to processing the first
                    [table_index] entries of the original list *)
                 (represents
                       (fold_left
                          (fun abst t_ptr =>
                             abstract_reassign_pointer
                               abst init_conc t_ptr (new_attrs attrs flags)
                               init_begin end_)
                          (firstn table_index t_ptrs)
                          init_abst) conc)
          else
            (* if !COMMIT, the abstract state hasn't changed *)
            represents init_abst conc)).
(*
  Definition mm_map_root_loop_invariant
             start_abst start_conc t_ptrs start_begin end_ attrs flags root_level
             (state : concrete_state * ptable_addr_t * size_t * bool * mpool)
    : Prop :=
    let '(s, begin, table_index, failed, ppool) := state in
     (* table_index stays in sync with [begin] *)
     (table_index = table_index_expression begin end_ root_level
      (* ...and [begin] increases monotonically *)
      /\ (start_begin <= begin)%N
      (* ...and the concrete state stays valid *)
      /\ is_valid s
      (* ..and [begin] is either equal to its starting value or is the start
         of a block *)
      /\ is_begin_or_block_start start_begin begin root_level
      (* ...and the page tables and local page pool don't overlap *)
      /\ locations_exclusive (ptable_deref s) ppool
      (* ...and the fallback of the local page pool is the global one *)
      /\ mpool_fallback ppool = Some (api_page_pool s)
      (* ...and local and global pools don't overlap *)
      /\ mpool_exclusive ppool (api_page_pool s)
      (* ...and we don't add/remove/change references to the root page tables  *)
      /\ (Forall (fun t_ptr =>
                    forall root_ptable stage,
                      root_ptable_matches_stage root_ptable stage ->
                      index_sequences_to_pointer
                        (ptable_deref start_conc) t_ptr root_ptable stage
                      = index_sequences_to_pointer
                          (ptable_deref s) t_ptr root_ptable stage)
                 t_ptrs)
      (* ...and if !COMMIT, the state hasn't changed meaningfully *)
      /\ (((flags & MM_FLAG_COMMIT) != 0) = false) -> concrete_state_equiv init_conc conc)
     (* and either we failed, or... *)
     /\ (failed = true \/
      (* ...and our concrete state is represented by the abstract state that
         corresponds to processing the first [table_index] entries of the original list *)
      /\ (represents
            (fold_left
               (fun abst t_ptr =>
                  abstract_reassign_pointer
                    abst start_conc t_ptr (new_attrs attrs flags)
                    start_begin end_)
               (firstn table_index t_ptrs)
               start_abst)
            s))).
*)

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

  Definition mm_map_root_loop_arguments_sig
             conc root_ptable begin end_ attrs level flags ppool :
    let state := (concrete_state * ptable_addr_t * nat * bool * mpool)%type in
    { loop_args : nat * (state -> bool) * state * (state -> state * bool) |
      mm_map_root conc root_ptable begin end_ attrs level flags ppool =
      let '(s, _, _, failed, ppool) :=
          @while_loop state (fst (fst (fst loop_args)))
                      (snd (fst (fst loop_args)))
                      (snd (fst loop_args)) (snd loop_args) in
      (negb failed, s, ppool) }.
  Proof.
    cbv [mm_map_root].
    match goal with
      |- context [@while_loop _ ?max_iter ?cond ?start ?body] =>
      exists (max_iter, cond, start, body) end.
    reflexivity.
  Defined.
  Definition mm_map_root_loop_arguments :=
    Eval cbv [proj1_sig mm_map_root_loop_arguments_sig] in
      (fun conc root_ptable begin end_ attrs level flags ppool =>
         proj1_sig
           (mm_map_root_loop_arguments_sig conc root_ptable begin end_ attrs level flags ppool)).
  Lemma mm_map_root_loop_arguments_eq
        conc root_ptable begin end_ attrs level flags ppool :
    mm_map_root conc root_ptable begin end_ attrs level flags ppool =
    let '(max_iter, cond, start, body) :=
        mm_map_root_loop_arguments
          conc root_ptable begin end_ attrs level flags ppool in
    let '(s, _, _, failed, ppool) :=
        @while_loop _ max_iter cond start body in
    (negb failed, s, ppool).
  Proof.
    change (mm_map_root_loop_arguments
              conc root_ptable begin end_ attrs level flags ppool) with
        (proj1_sig (mm_map_root_loop_arguments_sig
                      conc root_ptable begin end_ attrs level flags ppool)).
    pose proof
         (proj2_sig (mm_map_root_loop_arguments_sig
                      conc root_ptable begin end_ attrs level flags ppool)) as Hproj2.
    destruct
      (proj1_sig (mm_map_root_loop_arguments_sig
                    conc root_ptable begin end_ attrs level flags ppool)) as
        [ [ [ ? ? ] ? ] ? ].
    apply Hproj2.
  Qed.

  Lemma mm_map_root_loop_invariant_is_invariant :
    forall abst conc root_ptable begin end_ attrs root_level flags ppool,
      represents abst conc ->
      (* before calling mm_map_root, we have rounded end_ up to the nearest page,
       and we have capped it to not go beyond the end of the table *)
      (N.to_nat end_ <= mm_root_table_count flags * mm_entry_size root_level) ->
      (* we need to know we're actually at the root level *)
      is_root root_level flags ->
      ptable_is_root root_ptable flags ->
      (* and that the page tables and local page pool don't overlap *)
      locations_exclusive (ptable_deref conc) ppool ->
      (* fallback of the local page pool is the global one; they don't overlap *)
      mpool_fallback ppool = Some (api_page_pool conc) ->
      mpool_exclusive ppool (api_page_pool conc) ->
      (* and that [begin] and [end_ - 1] are on the same level *)
      mm_level_end begin root_level = mm_level_end (end_ - 1) root_level ->
      (* TODO : decide if we need this
      (begin < end_)%N -> *)
      let successful := (fun '(_, _, _, failed, _) => negb failed) in
      let loop_args := mm_map_root_loop_arguments
                         conc root_ptable begin end_ attrs root_level flags ppool in
      let t_ptrs := mm_page_table_from_pa (root root_ptable) in
      is_while_loop_invariant
        (mm_map_root_loop_invariant
           abst conc t_ptrs begin end_ attrs flags root_level)
        successful (snd (fst (fst loop_args))) (snd loop_args).
  Proof.
    cbv [is_while_loop_invariant mm_map_root_loop_invariant
                                 mm_map_root_loop_arguments];
      basics.

    (* useful facts about root_level *)
    pose proof (root_pos root_level flags ltac:(auto)).
    pose proof (root_le_max_level root_level flags ltac:(auto)).
    assert (root_level - 1 = max_level (stage_from_flags flags))
      by (cbv [is_root max_level mm_max_level stage_from_flags] in *; repeat break_match; solver).

    { (* loop only breaks when it failed or the loop condition is false *)
      simplify. }
    { (* invariant holds over loop *)
      simplify_no_break; repeat inversion_bool; subst;
        [ | | | | | | ]. (* 7 subgoals, one for each invariant clause *)

      (* find the current [begin] and assert its properties *)
      all:match goal with
          | H : is_begin_or_block_start _ ?x _ |- _ =>
            (* the level end hasn't changed *)
            assert (mm_level_end x root_level = mm_level_end (end_ - 1) root_level)
              by (rewrite (mm_level_end_eq begin x (end_ - 1)) by solver; solver);
              (* its index is in between the start and end addresses' indices *)
              assert (mm_index begin root_level <= mm_index x root_level <= mm_index (end_ - 1) root_level)
              by (split; apply mm_index_le_mono; solver);
              (* the index doesn't go past the end of the table *)
              assert (mm_index x root_level < length (mm_page_table_from_pa root_ptable.(root)))
                by (erewrite mm_page_table_from_pa_length by eauto;
                    apply mm_index_capped; [|solver]; apply mm_root_table_count_upper_bound)
          end.

      (* find the abstract state that represents the *current* concrete state,
         and give it a name so we can plug it in to mm_map_level proofs *)
      all:match goal with
          | H : if ?x then represents ?a1 ?c else represents ?a2 ?c
            |- context [mm_map_level ?c] =>
            let H:=fresh in
            remember (if x then a1 else a2) as current_abst eqn:H;
              assert (represents current_abst c) by simplify;
              clear H
          end.

      { (* table_index = table_index_expression *)
        cbv [table_index_expression] in *; simplify;
          pose proof mm_level_end_lt (end_ - 1) root_level;
          repeat match goal with
                 | _ => rewrite mm_index_start_of_next_block; try solver; [ ]
                 |  H : mm_level_end _ ?l = mm_level_end _ ?l |- _ =>
                    rewrite H
                 | _ => apply eq_S, eq_sym, mm_index_eq; solver
                 | _ => solver
                 end. }
      { (* init_begin <= begin *)
        simplify;
          match goal with
            |- (_ <= mm_start_of_next_block ?x _)%N => transitivity x; [solver|]
          end;
        apply N.lt_le_incl, mm_start_of_next_block_lt;
          auto using mm_entry_size_power_two. }
      { (* is_begin_or_block_start init_begin begin  *)
        simplify; cbv [is_begin_or_block_start]; right;
        apply mm_start_of_next_block_is_start;
          auto using mm_entry_size_power_two. }
      { (* locations_exclusive *)
        simplify.
        Search mm_map_level.
        { apply mm_map_level_locations_exclusive with (abst:=current_abst);
            try solver.
          cbv [table_index_expression].
          break_match; repeat inversion_bool; try solver; [ ].
          Search has_location_at_level.
          (* TODO : factor into lemma *)
          
        }
      { (* mpool_fallback *)
        simplify; autorewrite with push_fallback;
        cbv [reassign_pointer]; cbn [api_page_pool];
        match goal with
          | H : represents ?a ?c |- context [mm_map_level ?c] =>
            apply mm_map_level_fallback with (abst:=a) end;
          auto.
        3 :  { 
        Search mm_map_level.
        2:
        apply mm_map_level_fallback.

      }
      { (* mpool_exclusive *)
        cbv [reassign_pointer]; cbn [api_page_pool].
        apply mm_map_level_locations_mpool_exclusive; solver. }
      { (* index sequences don't change *)
        cbv [table_index_expression] in *; simplify; [ ].
        apply Forall_forall; intros.

        (* use the nodup to turn Nat.eq_dec into a decider on the mm_ptables *)
        match goal with
        | H : ptable_is_root _ _ |- _ =>
          pose proof H; apply ptable_is_root_In in H
        end.
        match goal with
        | H : root_ptable_matches_stage _ _ |- _ =>
          pose proof H; apply root_ptable_matches_stage_In in H
        end.
        repeat match goal with H : In ?x _ |- _ =>
                               apply In_nth_error in H; destruct H end.
        match goal with H1 : nth_error all_root_ptables ?i = Some ?x,
                             H2 : nth_error all_root_ptables ?j = Some ?y |- _ =>
                        destruct (Nat.eq_dec i j);
                          [ basics; replace x with y in * by solver | ]
        end;
          [ | erewrite !index_sequences_wrong_ptable by
                (try apply root_pointer_has_location; try solver;
                 eauto using NoDup_nth_error_neq, no_duplicate_ptables);
              reflexivity ].

        erewrite index_sequences_to_root by solver.
        erewrite index_sequences_to_root; try solver;
          try apply is_valid_root_wf; try solver;
            try apply mm_map_level_reassign_pointer; solver. }
      { (* represents step *)
  Qed.

  (* shortcut for using mm_map_root's loop invariant on weaker statements *)
  Lemma mm_map_root_loop_invariant_holds :
    forall abst conc root_ptable begin end_ attrs root_level flags ppool,
      represents abst conc ->
      has_location_at_root conc table level ->
      let cond := (fun '(_, begin, _, _, _) => (begin <? end_)%N) in
      forall P : _ -> Prop,
        (forall state,
            (cond state = false \/ negb (snd (fst state)) = false) ->
            mm_map_root_loop_invariant
              abst conc t_ptrs begin end_ attrs flags root_level ->
            P (let '(s, _, _, _, failed, ppool) := state in
               (negb failed, s, ppool))) ->
        P (mm_map_root conc root_ptable begin end_ attrs level flags ppool).
  Proof.
    cbv zeta; basics.
    eapply mm_map_level_loop_invariant_holds'; eauto; [ ].
    apply mm_map_level_loop_invariant_is_invariant; eauto.
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
    (* and that the page tables and local page pool don't overlap *)
    locations_exclusive (ptable_deref conc) ppool ->
    (* fallback of the local page pool is the global one; they don't overlap *)
    mpool_fallback ppool = Some (api_page_pool conc) ->
    mpool_exclusive ppool (api_page_pool conc) ->
    (* and that [begin] and [end_ - 1] are on the same level *)
    mm_level_end begin root_level = mm_level_end (end_ - 1) root_level ->
    forall abst,
      represents abst conc ->
      represents (fold_left
                    (fun abst t_ptr =>
                       abstract_reassign_pointer
                         abst conc t_ptr (new_attrs attrs flags)
                         begin end_)
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
    assert (root_level - 1 = max_level (stage_from_flags flags))
      by (cbv [is_root max_level mm_max_level stage_from_flags] in *; repeat break_match; solver).

    (* unfold [mm_map_root] to begin the real work *)
    cbv [mm_map_root] in *; simplify.

    (* use [while_loop_invariant] with [mm_map_root_loop_invariant] as the
       invariant *)
    let begin_index := constr:(mm_index begin root_level) in
    let t_ptrs := constr:(mm_page_table_from_pa t.(root)) in
    match goal with
    | |- context [@while_loop _ ?iter ?cond ?start ?body] =>
      eapply while_loop_invariant_strong with
          (inv:=mm_map_root_loop_invariant
                  abst conc t_ptrs begin end_ attrs flags root_level)
          (value:=(fun '(_,_,_,_,_,_) => N.to_nat (end_ - begin))
    end.
    
      assert (mm_map_root_loop_invariant
                abst conc t_ptrs begin end_ attrs flags root_level
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
      simplify_no_break.
      ; repeat inversion_bool; [ ].
      right.

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
        eapply reassign_pointer_represents; eauto; [ | | | | ].
        { eapply mm_map_level_represents; solver. }
        { apply has_location_nth_default with (flags:=flags); eauto. }
        { apply represents_valid_concrete; eexists;
            eapply mm_map_level_represents; solver. }
        { eapply mm_map_level_reassign_pointer; solver. }
        { cbv [level_from_indices]. cbv [length].
          match goal with |- context [?x + 2 - 1] =>
                          replace (x + 2 - 1) with (S x) by solver end.
          replace (root_level - 1) with (max_level (stage_from_flags flags)) by solver.
          eapply attrs_changed_in_range_proper;
            [ solve [eauto using mm_map_level_equiv, has_location_nth_default] .. | ].
          eapply mm_map_level_table_attrs;
            cbv [level_from_indices]; autorewrite with push_length;
              try apply Bool.negb_true_iff, N.eqb_neq;
              solver. } }
      { (* is_begin_or_block_start start_begin begin  *)
        cbv [is_begin_or_block_start]. right.
        apply mm_start_of_next_block_is_start;
          auto using mm_entry_size_power_two. }
      { (* locations_exclusive *)
        apply mm_map_level_locations_exclusive_reassign_local; solver. }
      { (* mpool_fallback *)
        simplify; autorewrite with push_fallback.
        cbv [reassign_pointer]; cbn [api_page_pool].
        apply mm_map_level_fallback; auto. }
      { (* mpool_exclusive *)
        cbv [reassign_pointer]; cbn [api_page_pool].
        apply mm_map_level_locations_mpool_exclusive; solver. }
      { (* index sequences don't change *)
        cbv [table_index_expression] in *; simplify; [ ].
        apply Forall_forall; intros.

        (* use the nodup to turn Nat.eq_dec into a decider on the mm_ptables *)
        match goal with
          | H : ptable_is_root _ _ |- _ =>
            pose proof H; apply ptable_is_root_In in H
        end.
        match goal with
          | H : root_ptable_matches_stage _ _ |- _ =>
            pose proof H; apply root_ptable_matches_stage_In in H
        end.
        repeat match goal with H : In ?x _ |- _ =>
                               apply In_nth_error in H; destruct H end.
        match goal with H1 : nth_error all_root_ptables ?i = Some ?x,
                             H2 : nth_error all_root_ptables ?j = Some ?y |- _ =>
                        destruct (Nat.eq_dec i j);
                          [ basics; replace x with y in * by solver | ]
        end;
          [ | erewrite !index_sequences_wrong_ptable by
                (try apply root_pointer_has_location; try solver;
                 eauto using NoDup_nth_error_neq, no_duplicate_ptables);
              reflexivity ].

        erewrite index_sequences_to_root by solver.
        erewrite index_sequences_to_root; try solver;
          try apply is_valid_root_wf; try solver;
            try apply mm_map_level_reassign_pointer; solver. }
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
        end.
        2: {
          (* TODO: the below is a copy-paste of the index-sequences case above, factor into a sublemma *)
          basics.

          match goal with |- context [nth_default ?d ?l ?i] =>
                          pose proof (nth_error_eq_default l i d ltac:(solver)) end.
          (* use the nodup to turn Nat.eq_dec into a decider on the mm_ptables *)
          match goal with
          | H : ptable_is_root _ _ |- _ =>
            pose proof H; apply ptable_is_root_In in H
          end.
          match goal with
          | H : root_ptable_matches_stage _ _ |- _ =>
            pose proof H; apply root_ptable_matches_stage_In in H
          end.
          repeat match goal with H : In ?x _ |- _ =>
                                 apply In_nth_error in H; destruct H end.
          match goal with H1 : nth_error all_root_ptables ?i = Some ?x,
                               H2 : nth_error all_root_ptables ?j = Some ?y |- _ =>
                          destruct (Nat.eq_dec i j);
                            [ basics; replace x with y in * by solver | ]
          end;
            [ | erewrite !index_sequences_wrong_ptable by
                  (try apply root_pointer_has_location; try solver;
                   eauto using NoDup_nth_error_neq, no_duplicate_ptables);
                reflexivity ].

          erewrite index_sequences_to_root by solver.
          erewrite index_sequences_to_root; try solver;
            try apply is_valid_root_wf; try solver;
              try apply mm_map_level_reassign_pointer; try solver.
          eapply concrete_equiv_valid, mm_map_level_equiv; solver. }

        eapply reassign_pointer_represents with (level := S (root_level - 1));
          try apply has_location_nth_default with (flags:=flags);
          try apply mm_map_level_reassign_pointer;
          try eapply concrete_equiv_valid, mm_map_level_equiv;
          try (eapply represents_proper; [ | solver];
               apply concrete_state_equiv_sym, mm_map_level_equiv);
          cbv [level_from_indices]; cbn [length]; try solver; [ ].
        eapply attrs_changed_in_range_proper;
          try apply mm_map_level_equiv;
          try eapply has_location_nth_default;
          try solver; [ ].
        destruct abst. (* so eauto doesn't insert abst where we don't want it *)
        match goal with
        | H : is_begin_or_block_start ?b ?x ?lvl |- _ =>
          destruct H
        end;
          [ subst;
            eapply mm_map_level_table_attrs;
            cbv [level_from_indices]; autorewrite with push_length;
            try apply Bool.negb_true_iff, N.eqb_neq; solver | ].
        eapply attrs_changed_in_range_block_start;
          try (replace (S (root_level - 1)) with root_level by lia; solver); [ ].
        eapply mm_map_level_table_attrs;
          cbv [level_from_indices]; autorewrite with push_length;
            try apply Bool.negb_true_iff, N.eqb_neq; solver. } }

    { (* Subgoal 2 : invariant holds at start *)
      right.
      cbv [table_index_expression] in *; simplify; [ | | ].
      { cbv [is_begin_or_block_start]; simplify. }
      { apply Forall_forall; intros.
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
    Unshelve.
    all:apply ppool.
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
