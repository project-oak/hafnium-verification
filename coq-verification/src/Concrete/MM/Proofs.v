Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.BinNat.
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
Require Import Hafnium.Concrete.Assumptions.Constants.
Require Import Hafnium.Concrete.Assumptions.Mpool.
Require Import Hafnium.Concrete.Assumptions.PageTables.
Require Import Hafnium.Concrete.MM.Datatypes.
Require Import Hafnium.Concrete.MM.Implementation.

(*** This file contains correctness proofs for the functions in mm.c, as
     transcribed in MM/Implementation.v ***)

Section Proofs.
  Context {ap : @abstract_state_parameters paddr_t nat}
          {cp : concrete_params}.

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
    end.
  Ltac simplify := repeat simplify_step.

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
        mm_map_level conc begin end_ pa attrs table level flags ppool in
    let success := fst (fst (fst ret)) in
    let table := snd (fst (fst ret)) in
    let conc' := snd (fst ret) in
    let ppool' := snd ret in
    let begin : nat := mm_index begin level in
    let end_ : nat := mm_index end_ level in
    has_uniform_attrs conc'.(ptable_deref) table level attrs begin end_.
  Admitted.

  (* placeholder; later there will be actual expressions for the new abstract
     states *)
  Axiom TODO : @abstract_state paddr_t nat.

  (* TODO: we know that all the mm_map_level steps succeed because we
  know that the whole thing succeeds. But how do we use that in the
  invariant? *)
  Definition mm_map_root_loop_invariant
             start_abst start_conc t_ptrs start_begin attrs root_level
             (state : concrete_state * ptable_addr_t * size_t * bool * mpool)
    : Prop :=
    let '(s, begin, table_index, failed, ppool) := state in
    let index := mm_index begin root_level in
    table_index = index /\
    (failed = true \/
     represents
       (fold_right
          (fun t_ptr abst =>
             abstract_reassign_pointer abst start_conc t_ptr attrs start_begin index)
          start_abst
          (firstn table_index t_ptrs))
       s).

  (* TODO: move *)
  Lemma N_lnot_0_r a : N.lnot a 0 = a.
  Proof. destruct a; reflexivity. Qed.

  (* TODO: move *)
  Lemma N_div2_lnot a n : N.div2 (N.lnot a n) = N.lnot (N.div2 a) (N.pred n).
  Admitted. (* TODO *)
    
  (* TODO: move *)
  Lemma N_lnot_shiftr a n m : ((N.lnot a n >> m) = N.lnot (a >> m) (n - m))%N.
  Proof.
    rewrite <-(Nnat.N2Nat.id m).
    induction (N.to_nat m).
    { rewrite !N.shiftr_0_r.
      rewrite N.sub_0_r. reflexivity. }
    { rewrite Nnat.Nat2N.inj_succ.
      rewrite !N.shiftr_succ_r.
      rewrite N.sub_succ_r.
      rewrite <-N_div2_lnot.
      solver. }
  Qed.

  (* TODO: move *)
  Lemma N_log2_add_shiftl_1 a b : (b <= N.log2 (a + (1 << b)))%N.
  Admitted. (* TODO *)

  (* TODO: include 0 < PAGE_BITS axiom *)
  Lemma mm_start_of_next_block_shift a level :
    (0 < PAGE_BITS)%N ->
    (mm_start_of_next_block a (mm_entry_size level)
                            >> (PAGE_BITS + level * PAGE_LEVEL_BITS))%N =
    ((a >> (PAGE_BITS + level * PAGE_LEVEL_BITS)) + 1)%N.
  Proof.
    intros.
    cbv [mm_start_of_next_block mm_entry_size].
    rewrite !Nnat.N2Nat.id, N.shiftr_land, N_lnot_shiftr.
    rewrite N.shiftr_eq_0 with (a:=((_ << _) - 1)%N) by
        (rewrite N.sub_1_r, N.shiftl_1_l, N.log2_pred_pow2 by lia; lia).
    rewrite N.lnot_0_l.
    match goal with
    | |- context [((_ + (_ << ?x)) >> ?x)%N] =>
      pose proof (N_log2_add_shiftl_1 a x);
        assert ((1 << x) <> 0)%N by (rewrite N.shiftl_eq_0_iff; lia)
    end.
    rewrite N.land_ones_low by (rewrite N.log2_shiftr, N.size_log2 by lia; lia).
    rewrite !N.shiftr_div_pow2, !N.shiftl_mul_pow2.
    rewrite N.div_add by (apply N.pow_nonzero; lia).
    lia.
  Qed.

  Lemma mm_index_start_of_next_block a level :
    mm_index (mm_start_of_next_block a (mm_entry_size level)) level
    = S (mm_index a level).
  Proof.
    cbv [mm_index].
    rewrite mm_start_of_next_block_shift.
    remember ((1 << PAGE_LEVEL_BITS) - 1)%N as mask.
    remember (PAGE_BITS + level * PAGE_LEVEL_BITS)%N as B.
    (* TODO: won't be *hard*, but will be annoying. Will likely require a
       precondition in terms of mm_level_end. *)
  Admitted.

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
    let t_ptrs := mm_page_table_from_pa t.(root) in
    let begin_index := mm_index begin root_level in
    let end_index := mm_index end_ root_level in
    success = true ->
    ((flags & MM_FLAG_COMMIT) != 0)%N = true ->
    (begin <= end_)%N ->
    end_index < length t_ptrs ->
    forall abst,
      represents abst conc ->
      represents (fold_right
                    (fun t_ptr abst =>
                       abstract_reassign_pointer
                         abst conc t_ptr attrs begin_index end_index)
                    abst t_ptrs)
                 conc'.
  Proof.
    cbv zeta. cbv [mm_map_root].
    simplify.

    let t_ptrs := constr:(mm_page_table_from_pa t.(root)) in
    let start_begin := constr:(mm_index begin root_level) in
    match goal with
    | |- context [@while_loop _ ?iter ?cond ?start ?body] =>
      assert (mm_map_root_loop_invariant
                abst conc t_ptrs start_begin attrs root_level
                (@while_loop _ iter cond start body));
        [ apply while_loop_invariant | ]
    end;
      cbv [mm_map_root_loop_invariant] in *; simplify;
        repeat inversion_bool;
        rewrite ?mm_map_level_represents.
    { rewrite mm_index_start_of_next_block; reflexivity. }
    { rewrite mm_index_start_of_next_block; reflexivity. }
    { right.
      cbn [firstn fold_right].
      rewrite ?mm_map_level_represents.
        cbv [mm_map_root_loop_invariant] in *; simplify.
        right.
          rewrite ?mm_map_level_represents
    end.
    Check while_loop_invariant.
    { (* TODO: in this case, the map_level step failed, so we can't have returned success. *)
      
      Check reassign_pointer_represents.
      Print mm_page_table_from_pa.
      Check ptable_pointer_from_address.
      SearchAbout s.
    3:rewrite abstract_reassign_pointer_trivial; solver.
    1-2: admit. (* mm_map_level layer *)

    match goal with
    | H : represents (?f ?i) ?x |- represents (?f ?j) ?x =>
      assert (i = j); [clear H | solver]
    end.


    apply f_equal2; [|reflexivity].
    apply Nnat.N2Nat.inj_iff.
    match goal with
    | |- context [@while_loop _ ?iter ?cond ?st ?body] =>
      rewrite <- (while_loop_end_exact iter body
                                       (fun '(_,_,_,failed,_) => negb failed)
                                       (fun '(_,begin,_,_,_) => N.to_nat begin)
                                       (N.to_nat end_)) with (start:=st);
        simplify
    end.

    {
    repeat (f_equal;
            try
              (apply while_loop_proper_cond;
               repeat match goal with
                      | _ => progress basics
                      | p : _ * _ |- _ => destruct p
                      | _ => apply N.to_nat_ltb
                      | _ => solver
                      end)). }
    6 : {
    rewrite while_loop_proper_cond with
        (cond':=fun '(_,begin,_,_,_) => N.to_nat begin <? N.to_nat end_) in * by
        repeat match goal with
               | _ => progress basics
               | p : _ * _ |- _ => destruct p
               | _ => apply N.to_nat_ltb
               | _ => solver
               end.
    solver. }

    { cbv [break continue] in *; solver. }
    { admit. (* TODO: assume this about mm_start_of_next_block, that its results are > input *) }
    { admit. (* TODO: assume this about mm_start_of_next_block, that it won't skip pages if end_ is aligned *) }
    { apply Nat.leb_le. rewrite Nat.leb_compare.
      rewrite <-Nnat.N2Nat.inj_compare. break_match; solver. }
    { rewrite Nnat.N2Nat.inj_sub; solver. }
  Admitted.

  Lemma mm_ptable_identity_update_represents
        (conc : concrete_state)
        t pa_begin pa_end attrs flags ppool :
    forall abst,
      represents abst conc ->
      represents TODO
                 (snd (fst (mm_ptable_identity_update
                              conc t pa_begin pa_end attrs flags ppool))).
  Admitted.

  Lemma mm_identity_map_represents
        (conc : concrete_state)
        begin end_ mode ppool :
    preserves_represents_valid
      (fun conc => snd (fst (mm_identity_map conc begin end_ mode ppool))).
  Admitted.

  Lemma mm_defrag_represents
        (conc : concrete_state)
        ppool :
    preserves_represents_valid
      (fun conc => fst (mm_defrag conc ppool)).
  Admitted.

  Lemma mm_unmap_represents
        (conc : concrete_state)
        begin end_ ppool :
    preserves_represents_valid
      (fun conc => snd (fst (mm_unmap conc begin end_ ppool))).
  Admitted.
End Proofs.
