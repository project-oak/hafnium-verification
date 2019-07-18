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
    | H : break = continue |- _ => cbv [break continue] in H; solver
    | H : continue = break |- _ => cbv [break continue] in H; solver
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

  (* placeholder; later there will be actual expressions for the new abstract
     states *)
  Axiom TODO : @abstract_state paddr_t nat.

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

  Definition is_start_of_block (a : uintvaddr_t) (block_size : size_t) : Prop :=
    (a & (block_size - 1))%N = 0.

  Lemma mm_start_of_next_block_is_start a block_size :
    is_start_of_block (mm_start_of_next_block a block_size) block_size.
  Admitted. (* TODO *)

  (* dumb wrapper for one of the invariants so it doesn't get split too early *)
  Definition is_begin_or_block_start
             (start_begin begin : ptable_addr_t) root_level : Prop :=
      (begin = start_begin \/ is_start_of_block begin (mm_entry_size root_level)).

  Definition mm_map_root_loop_invariant
             start_abst start_conc t_ptrs start_begin end_ attrs root_level
             (state : concrete_state * ptable_addr_t * size_t * bool * mpool)
    : Prop :=
    let '(s, begin, table_index, failed, ppool) := state in
    let end_index := mm_index end_ root_level in
    (failed = true \/
     (table_index = mm_index begin root_level
      /\ (start_begin <= begin)%N
      /\ (begin <= mm_level_end end_ root_level)%N
      /\ pointers_ok s ppool
      /\ is_begin_or_block_start start_begin begin root_level
      /\ (Forall (fun t_ptr =>
                    Forall
                      (fun root_ptable =>
                         index_sequences_to_pointer
                           start_conc.(ptable_deref) t_ptr root_ptable
                         = index_sequences_to_pointer
                             s.(ptable_deref) t_ptr root_ptable)
                      all_root_ptables)
                 t_ptrs)
      /\ (represents
            (fold_left
               (fun abst t_ptr =>
                  abstract_reassign_pointer
                    abst start_conc t_ptr attrs start_begin end_)
               (firstn table_index t_ptrs)
               start_abst)
            s))).

  (* TODO: include 0 < PAGE_BITS axiom *)
  Lemma mm_start_of_next_block_shift a level :
    (0 < PAGE_BITS)%N ->
    (mm_start_of_next_block a (mm_entry_size level)
                            >> (PAGE_BITS + level * PAGE_LEVEL_BITS))%N =
    ((a >> (PAGE_BITS + level * PAGE_LEVEL_BITS)) + 1)%N.
  Proof.
    intros.
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

  Lemma mm_start_of_next_block_lt a block_size :
    (a < mm_start_of_next_block a block_size)%N.
  Admitted. (* TODO *)

  Lemma mm_start_of_next_block_level_end a level :
    (mm_start_of_next_block a (mm_entry_size level) <= mm_level_end a level)%N.
  Admitted. (* TODO *)

  Lemma mm_index_le_mono a b level :
    (a <= b)%N ->
    (b <= mm_level_end a level)%N ->
    mm_index a level <= mm_index b level.
  Admitted. (* TODO *)

  Lemma mm_level_end_le a level : (a <= mm_level_end a level)%N.
  Admitted. (* TODO *)

  Lemma mm_index_lt_mono_start (a b : ptable_addr_t) (level : nat) :
    is_start_of_block a (mm_entry_size level) ->
    (b < a)%N ->
    mm_index b level < mm_index a level.
  Admitted. (* TODO *)

  Definition is_root (level : nat) : Prop :=
    exists flags, level = mm_max_level flags + 1.

  Lemma root_pos level : is_root level -> 0 < level.
  Proof. cbv [is_root]; simplify. Qed.

  (* At the root level, every address has the same level_end *)
  Lemma mm_level_end_root_eq root_level :
    is_root root_level ->
    forall a b, mm_level_end a root_level = mm_level_end b root_level.
  Admitted. (* TODO *)

  (* table pointers that come before the index of [begin] don't contain any
     addresses in the range [begin...end_) *)
  Lemma root_mm_index_out_of_range_low conc begin end_ root_level root_ptable:
    In root_ptable all_root_ptables ->
    is_root root_level ->
    forall i,
      i <= mm_index begin root_level ->
      Forall (fun ptr => no_addresses_in_range (ptable_deref conc) ptr begin end_)
             (firstn i (mm_page_table_from_pa root_ptable.(root))).
  Admitted. (* TODO *)

  (* table pointers that come after the index of [end_ - 1] don't contain any
     addresses in the range [begin...end_) *)
  Lemma root_mm_index_out_of_range_high conc begin end_ root_level root_ptable:
    In root_ptable all_root_ptables ->
    is_root root_level ->
    forall i,
      mm_index (end_ - 1) root_level < i ->
      Forall (fun ptr => no_addresses_in_range (ptable_deref conc) ptr begin end_)
             (skipn i (mm_page_table_from_pa root_ptable.(root))).
  Admitted. (* TODO *)

  (* makes proof state more readable *)
  Local Ltac remember_while_loop :=
    let RET := fresh "RET" in
    match goal with
    | |- context [@while_loop _ ?iter ?cond ?start ?body] =>
      remember (@while_loop _ iter cond start body) as RET
    | H : context [@while_loop _ ?iter ?cond ?start ?body] |- _ =>
      remember (@while_loop _ iter cond start body) as RET
    end.

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
    let end_index := mm_index end_ root_level in
    success = true ->
    ((flags & MM_FLAG_COMMIT) != 0)%N = true ->
    (* TODO : maybe can remove the begin <= end precondition; if it's not true the loop just doesn't happen *)
    (begin < end_)%N ->
    (* before calling mm_map_root, we have rounded end_ up to the nearest page,
       and we have capped it to not go beyond the end of the table *)
    end_index < length (mm_page_table_from_pa t.(root)) ->
    (* we need to know we're actually at the root level *)
    is_root root_level ->
    In t all_root_ptables ->
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
    cbv zeta. cbv [mm_map_root].
    simplify.

    pose proof (root_pos root_level ltac:(auto)). 

    let begin_index := constr:(mm_index begin root_level) in
    let end_index := constr:(mm_index end_ root_level) in
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
    { (* main case : prove invariant holds over step *)

      (* conclude that mm_map_level succeeded *)
      simplify; repeat inversion_bool; [ ].
      right; rewrite !mm_map_level_represents.

      (* find the current [begin] and assert that its index is in between the
           start and end addresses' indices *)
      pose proof (mm_level_end_root_eq root_level ltac:(assumption) begin end_).
      match goal with
      | H : is_begin_or_block_start _ ?x _ |- _ =>
        assert (mm_index begin root_level <= mm_index x root_level)
          by (apply mm_index_le_mono; solver);
          assert (mm_index x root_level <= mm_index end_ root_level)
          by (apply mm_index_le_mono; [ solver | ];
              erewrite mm_level_end_root_eq by auto;
              apply mm_level_end_le)
      end.

      (* split into the invariant clauses *)
      simplify.

      { (* table_index = mm_index begin root_level *)
        rewrite mm_index_start_of_next_block; reflexivity. }
      { (* start_begin <= begin *)
        match goal with
          |- (_ <= mm_start_of_next_block ?x _)%N => transitivity x; [solver|]
        end.
        apply N.lt_le_incl.
        apply mm_start_of_next_block_lt. }
      { (* begin <= mm_level_end end_ root_level *)
        erewrite mm_level_end_root_eq by eauto.
        apply mm_start_of_next_block_level_end. }
      { (* pointers_ok s ppool *)
        apply mm_map_level_pointers_ok.
        auto. }
      { (* is_begin_or_block_start start_begin begin  *)
        cbv [is_begin_or_block_start].
        right. apply mm_start_of_next_block_is_start. }
      { (* index sequences don't change *)
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
    { (* invariant holds at start *)
      right. simplify.
      {  erewrite mm_level_end_root_eq by eauto; apply mm_level_end_le. }
      {  cbv [is_begin_or_block_start]; solver. }
      { apply Forall_forall; intros.
        apply Forall_forall; intros.
        reflexivity. }
      { eapply represents_proper_abstr; [|solver].
        apply abstract_reassign_pointer_low.
        eapply root_mm_index_out_of_range_low; solver. } }
    { (* invariant implies correctness *)
      repeat inversion_bool; simplify; [ ].
      match goal with
      | |- context [@while_loop _ ?iter ?cond ?st ?body] =>
          assert (cond (@while_loop _ iter cond st body) = false);
            [ apply (while_loop_completed iter cond body
                                          (fun '(_,_,_,failed,_) => negb failed)
                                          (fun '(_,begin,_,_,_) => N.to_nat begin)
                                          (N.to_nat end_))
            | remember (@while_loop _ iter cond st body) as RET]
      end.

      (* speeds up and simplifies proofs to forget that the thing we're talking about is a loop *)
      all:remember_while_loop.
      all:clear HeqRET.

      (* get rid of all but 2 goals *)
      all:simplify.
      all:try apply N.to_nat_ltb.
      all:try apply Bool.negb_true_iff.
      all:simplify.
      all:try solve [rewrite ?Nnat.N2Nat.inj_sub; solver].

      { apply N.to_nat_lt_iff.
        apply mm_start_of_next_block_lt. } 
      { match goal with
        | H : represents ?x ?c |- represents ?y ?c =>
          apply (represents_proper_abstr x y c); [|solver]
        end.
        apply abstract_reassign_pointer_high.
        eapply root_mm_index_out_of_range_high; try solver; [ ].
        repeat inversion_bool.
        cbv [is_begin_or_block_start] in *.
        apply mm_index_lt_mono_start; simplify. } }
  Qed.

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
