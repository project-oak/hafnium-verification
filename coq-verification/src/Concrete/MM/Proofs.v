Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
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
        t begin end_ attrs table level flags ppool :
    (snd (fst (mm_map_level
                 conc t begin end_ attrs table level flags ppool))) = conc.
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

  (* placeholder; later there will be actual expressions for the new abstract
     states *)
  Axiom TODO : @abstract_state paddr_t nat.

  Definition mm_map_root_loop_invariant
             start_abst start_conc t_ptr start_begin attrs root_level
             (state : concrete_state * ptable_addr_t * size_t * bool * mpool)
    : Prop :=
    let '(s, begin, table_index, failed, ppool) := state in
    let index := mm_index begin root_level in
    represents
      (abstract_reassign_pointer start_abst start_conc t_ptr attrs start_begin index)
      s.

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
    let t_ptr := ptable_pointer_from_address t.(root) in
    let begin_index := mm_index begin root_level in
    let end_index := mm_index end_ root_level in
    success = true ->
    ((flags & MM_FLAG_COMMIT) != 0)%N = true ->
    (begin <= end_)%N ->
    forall abst,
      represents abst conc ->
      represents (abstract_reassign_pointer
                    abst conc t_ptr attrs begin_index end_index) conc'.
  Proof.
    cbv zeta. cbv [mm_map_root].
    simplify.

    let t_ptr := constr:(ptable_pointer_from_address t.(root)) in
    let start_begin := constr:(mm_index begin root_level) in
    match goal with
    | |- context [@while_loop _ ?iter ?cond ?start ?body] =>
      assert (mm_map_root_loop_invariant
                abst conc t_ptr start_begin attrs root_level
                (@while_loop _ iter cond start body));
        [ apply while_loop_invariant | ];
        cbv [mm_map_root_loop_invariant] in *; simplify
    end.
    3:admit. (* TODO: proof that if begin and end are the same then has_uniform_attrs is trivially true *)
    all:rewrite ?mm_map_level_represents.
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
