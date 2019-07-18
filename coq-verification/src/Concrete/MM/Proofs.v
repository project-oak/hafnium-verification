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

  (* placeholder; later there will be actual expressions for the new abstract
     states *)
  Axiom TODO : @abstract_state paddr_t nat.


  (* Need to figure out alignment situation!
     - condition of while loop is [end <= begin]
     - [end] is rounded *up* to the nearest page
     - [mm_start_of_next_block]...what does it do? I think it gets the address of
       the next table entry at the given level, as suggested by incrementation of
       [table_index]
        * it zeroes out all the bits below the provided block size, which is mm_entry_size level, so yes
     
     if [end] is not aligned to the entry size, then what will happen?
        well, we'll eventually get to a point where [mm_index begin level = mm_index end level], but begin < end because begin is aligned
        we'll do that reassignment and the range checks will keep things honest
        then mm_index begin level = S (mm_index end level) and begin >= end; break

     if [end] is aligned, then what will happen?
        as soon as [mm_index begin level = mm_index end level], [begin = end] and we break

     so...while_loop_end_exact is NOT the right thing, quite. We don't get
     [begin = end_]; we get [begin >= end_] and
     [mm_index begin level = if end_aligned_to_entry_size
                             then mm_index end level
                             else S (mm_index end level) ]
     
     if we know [mm_index begin level <= S (mm_index end level)], does that help?

   *)

  (* maybe we need some part of the concrete state to say where each
  ptable_pointer is, exactly one location. They can be either in mpool
  or somewhere in a page table, but this would enforce by construction
  that they're not repeated... *)
  Axiom pointer_in_table :
    (Datatypes.ptable_pointer -> mm_page_table) ->
    Datatypes.ptable_pointer -> mm_page_table -> Prop.


  Definition deref_noncircular (c : concrete_state) : Prop :=
    forall ptr,
      ~ pointer_in_table c.(ptable_deref) ptr (c.(ptable_deref) ptr).

  Axiom mpool_contains : mpool -> Datatypes.ptable_pointer -> Prop.

  Definition pointers_ok (c : concrete_state) (ppool : mpool) : Prop :=
    deref_noncircular c
    /\ (forall ptr,
           mpool_contains ppool ptr <->
           (forall ptr2, ~ pointer_in_table c.(ptable_deref) ptr (c.(ptable_deref) ptr2))).

  (* TODO : is this the right approach? *)
  Lemma mm_map_level_noncircular c begin end_ pa attrs ptr level flags ppool :
    pointers_ok c ppool ->
    let ret := mm_map_level
                 c begin end_ pa attrs (ptable_deref c ptr) level flags ppool in
    let table := snd (fst (fst ret)) in
    ~ pointer_in_table (ptable_deref c) ptr table.
  Admitted. (* TODO *)
 
  Definition is_start_of_block (a : ptable_addr_t) (level : nat) : Prop :=
    (a & (mm_entry_size level - 1))%N = 0.

  Lemma mm_start_of_next_block_is_start a level :
    is_start_of_block (mm_start_of_next_block a (mm_entry_size level)) level.
  Admitted. (* TODO *)

  (* dumb wrapper for one of the invariants so it doesn't get split too early *)
  Definition is_begin_or_block_start
             (start_begin begin : ptable_addr_t) root_level : Prop :=
      (begin = start_begin \/ is_start_of_block begin root_level).

  (* TODO: we're not actually using the starting concrete state all
  the time; the concrete state has to change. But how exactly can we
  encode that? *)
  (* In reality, it shouldn't matter that the concrete state is
  changing because we only care about the subset of it that leads to
  the pointers we're changing, and those pointers should all be on the
  same level and not be in each other's paths. Can we encode this by
  passing in the index sequences to the pointer, perhaps, instead of
  the entire concrete state? *)
  (* Can we say each pointer has exactly one index sequence and they
  don't affect each other's index sequences and then pass in an index
  sequence to abstract_reassign_pointer instead of a concrete state
  and a pointer? *)
  (* Should we do away with ptable_pointer entirely? *)
  (* what if, instead of ptable_pointer, we had something that
  indicated position-from-root? Something like the index sequences? *)
  (* the beauty of the current solution is that it *does* remap every
  location exactly as happens in concrete state. But can we preserve
  that beauty? Where exactly would we run into problems with allowing
  for repeats of the same pointer? *)
  (* well, somewhere we need to know that the concrete state doesn't
  change stuff in random other places...we *need* the property that
  ptable_pointers don't repeat themselves *)
  (* in this case, that reasoning would look like:
     - every ptable_pointer has exactly one index_sequence from exactly one table (reassign_pointer preserves that property because mm_map_level output fits certain conditions)
     - none of the reassignments we do will change each other's index sequence, because they can't change anything shorter than themselves
     - if the index_sequence for the pointer passed into abstract_reassign_pointer hasn't changed, we can switch out concrete states
   *)
  Definition mm_map_root_loop_invariant
             start_abst start_conc t_ptrs start_begin end_ attrs root_level
             (state : concrete_state * ptable_addr_t * size_t * bool * mpool)
    : Prop :=
    let '(s, begin, table_index, failed, ppool) := state in
    let index := table_index - mm_index start_begin root_level in
    let end_index := mm_index end_ root_level in
    (failed = true \/
     (table_index = mm_index begin root_level
      /\ (start_begin <= begin)%N
      /\ (begin <= mm_level_end end_ root_level)%N
      /\ pointers_ok s ppool
      /\ is_begin_or_block_start start_begin begin root_level
      /\ (Forall (fun t_ptr =>
                    Forall
                      (fun root_ptr =>
                         index_sequences_to_pointer
                           start_conc.(ptable_deref) t_ptr root_ptr
                         = index_sequences_to_pointer
                             s.(ptable_deref) t_ptr root_ptr)
                      (hafnium_root_ptable :: map vm_root_ptable vms))
                 t_ptrs)
      /\ (represents
            (fold_left
               (fun abst t_ptr =>
                  abstract_reassign_pointer
                    abst start_conc t_ptr attrs start_begin end_)
               (firstn index t_ptrs)
               start_abst)
            s))).

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

  Lemma mm_index_le_mono a b level :
    (a <= b)%N ->
    (b <= mm_level_end a level)%N ->
    mm_index a level <= mm_index b level.
  Admitted. (* TODO *)

  (* TODO: move *)
  Lemma firstn_snoc {A} i ls d :
    i < length ls ->
    @firstn A (S i) ls = firstn i ls ++ (nth_default d ls i :: nil).
  Admitted. (* TODO *)

  (* TODO: move *)
  Lemma abstract_reassign_pointer_for_entity_change_concrete
        abst conc conc' ptr owned valid e root_ptr begin end_ :
    index_sequences_to_pointer conc.(ptable_deref) ptr root_ptr
    = index_sequences_to_pointer conc'.(ptable_deref) ptr root_ptr ->
    abstract_reassign_pointer_for_entity
      abst conc ptr owned valid e root_ptr begin end_
    = abstract_reassign_pointer_for_entity
        abst conc' ptr owned valid e root_ptr begin end_.
  Proof.
    cbv beta iota delta [abstract_reassign_pointer_for_entity].
    intro Heq. rewrite Heq. reflexivity.
  Qed.

  (* TODO : move *)
  Lemma fold_right_ext {A B} (f g : A -> B -> B) b ls :
    (forall a b, In a ls -> f a b = g a b) ->
    fold_right f b ls = fold_right g b ls.
  Admitted. (* TODO *)

  (* TODO : move *)
  Lemma fold_left_ext {A B} (f g : B -> A -> B) b ls :
    (forall a b, In b ls -> f a b = g a b) ->
    fold_left f ls b = fold_left g ls b.
  Admitted. (* TODO *)

  (* TODO : move *)
  Lemma fold_left_nil {A B} (f : B -> A -> B) b :
    fold_left f nil b = b.
  Proof. reflexivity. Qed.
  Hint Rewrite @fold_left_nil : push_fold_left.

  (* TODO : move *)
  Lemma Forall_map {A B} (P : B -> Prop) (f : A -> B) ls :
    Forall P (map f ls) -> Forall (fun a => P (f a)) ls.
  Admitted. (* TODO *)

  (* TODO: move *)
  Lemma abstract_reassign_pointer_change_concrete
        abst conc conc' ptr attrs begin_index end_index :
    Forall (fun root_ptr =>
              index_sequences_to_pointer conc.(ptable_deref) ptr root_ptr
              = index_sequences_to_pointer conc'.(ptable_deref) ptr root_ptr)
            (hafnium_root_ptable :: map vm_root_ptable vms) ->
    abstract_reassign_pointer abst conc ptr attrs begin_index end_index
    = abstract_reassign_pointer abst conc' ptr attrs begin_index end_index.
  Proof.
    cbv [abstract_reassign_pointer].
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

  (* TODO : move *)
  Lemma nth_default_skipn {A} (d:A) i j ls :
    nth_default d (skipn i ls) j = nth_default d ls (j + i).
  Admitted. (* TODO *)

  (* TODO : move *)
  Lemma nth_default_firstn_low {A} (d:A) i j ls :
    j < i ->
    nth_default d (firstn i ls) j = nth_default d ls j.
  Admitted. (* TODO *)

  Lemma mm_level_end_le a level : (a <= mm_level_end a level)%N.
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

  (* TODO : move *)
  Lemma In_nth_default_firstn {A} (d:A) i j ls :
    i < j ->
    In (nth_default d ls i) (firstn j ls).
  Admitted. (* TODO *)

  (* TODO : move *)
  Lemma In_nth_default_skipn {A} (d:A) i j ls :
    j <= i ->
    In (nth_default d ls i) (skipn j ls).
  Admitted. (* TODO *)

  (* TODO : move *)
  Lemma In_nth_default_skipn_firstn {A} (d:A) i j k ls :
    j <= i < k->
    In (nth_default d ls i) (skipn j (firstn k ls)).
  Admitted. (* TODO *)

  (* TODO : move *)
  (* has_uniform_attrs doesn't care if we reassign the pointer we started from *)
  (* TODO : will need some kind of precondition saying the pointer doesn't repeat *)
  Lemma has_uniform_attrs_reassign_pointer c ptr new_table t level attrs begin end_:
    ~ pointer_in_table (ptable_deref c) ptr t ->
    has_uniform_attrs (ptable_deref c) t level attrs begin end_ ->
    has_uniform_attrs
      (ptable_deref (reassign_pointer c ptr new_table))
      t level attrs begin end_.
  Admitted. (* TODO *)

  (* TODO: move *)
  (* has_uniform_attrs is trivially true for things before the start of the given
     table; therefore, we can arbitrarily expand the range in that direction. *)
  Lemma has_uniform_attrs_expand_range
        deref table level attrs begin start end_ :
    is_start_of_block start (S level) ->
    (begin <= start)%N ->
    has_uniform_attrs deref table level attrs start end_ ->
    has_uniform_attrs deref table level attrs begin end_.
  Admitted. (* TODO *)

  (* TODO : move *)
  (* TODO : probably will need preconditions about pointers being noncircular *)
  Lemma abstract_reassign_pointer_root abst conc root_ptr attrs begin end_ :
    represents
      (fold_left
         (fun abst t_ptr =>
            abstract_reassign_pointer abst conc t_ptr attrs begin end_)
         (mm_page_table_from_pa root_ptr)
         abst)
      conc ->
    represents
      (abstract_reassign_pointer abst conc (ptable_pointer_from_address root_ptr)
                                 attrs begin end_)
      conc.
  Admitted. (* TODO *)

  (* TODO:
     This proof says only that if success = true and commit = true
     then the abstract state changed. We need two more proofs for full
     correctness; one saying that if commit = false, the state is
     unchanged, and another saying that if success = true and commit =
     false, then success = true when the function is run again on the
     (unchanged) output state. *)
  (* mm_level_end with level=root_level should be the end of the *root* ptable -- that means
     mm_level_end begin root_level = mm_level_end end_ root_level *)
  (* since abstract_reassign_pointer doesn't do anything if the
  addresses given are out of range, we can reassign from root *)
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
    let t_ptrs :=
        skipn begin_index
              (firstn (S end_index) (mm_page_table_from_pa t.(root))) in
    success = true ->
    ((flags & MM_FLAG_COMMIT) != 0)%N = true ->
    (begin <= end_)%N ->
    (* before calling mm_map_root, we have rounded end_ up to the nearest page,
       and we have capped it to not go beyond the end of the table *)
    end_index < length (mm_page_table_from_pa t.(root)) ->
    (* we need to know we're actually at the root level *)
    is_root root_level ->
    (* nothing weird and circular going on with pointers *)
    pointers_ok conc ppool ->
    forall abst,
      represents abst conc ->
      represents (fold_left
                    (fun abst t_ptr =>
                       abstract_reassign_pointer
                         abst conc t_ptr attrs begin end_)
                    t_ptrs abst)
                 conc'.
  Proof.
    cbv zeta. cbv [mm_map_root].
    simplify.

    pose proof (root_pos root_level ltac:(auto)). 

    let begin_index := constr:(mm_index begin root_level) in
    let end_index := constr:(mm_index end_ root_level) in
    let t_ptrs := constr:(skipn begin_index
                                (firstn (S end_index)
                                        (mm_page_table_from_pa t.(root)))) in
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

      (* split into the invariant clauses *)
      simplify.

      { (* table_index = mm_index begin root_level *)
        rewrite mm_index_start_of_next_block; reflexivity. }
      { (* start_begin <= begin *)
        match goal with
          |- (_ <= mm_start_of_next_block ?x _)%N => transitivity x; [solver|]
        end.
        admit. (* TODO : factor out mm_start_of_next_block proof saying it obeys le *) }
      { (* begin <= mm_level_end end_ root_level *)
        admit. (* TODO: factor out a lemma about mm_start_of_next_block saying that it won't skip over the level end *) }
      { (* pointers_ok s ppool *)
        admit. (* TODO : factor out mm_map_level proof *) }
      { (* is_begin_or_block_start start_begin begin  *)
        cbv [is_begin_or_block_start].
        right. apply mm_start_of_next_block_is_start. }
      { (* index sequences don't change *)
        apply Forall_forall; intros.
        apply Forall_forall; intros.
        admit.
        (* TODO: factor out a lemma about mm_map_level saying that reassigning the pointer is OK wrt existing pointer index sequences
           (reasoning: mm_map_level is not going to add any new
           pointers to the state unless it gets them from mpool, which
           won't give out stuff that's already there -- probably will
           require precondition saying mpool doesn't have any pointers
           that are referenced from any roots) *) }
      { (* represents step *)
        pose proof (mm_level_end_root_eq root_level ltac:(assumption) begin end_).

        (* find the current [begin] and assert that its index is in between the
           start and end addresses' indices *)
        match goal with
        | H : is_begin_or_block_start _ ?x _ |- _ =>
          assert (mm_index begin root_level <= mm_index x root_level)
            by (apply mm_index_le_mono; solver);
          assert (mm_index x root_level <= mm_index end_ root_level)
            by (apply mm_index_le_mono; [ solver | ];
                erewrite mm_level_end_root_eq by auto;
                apply mm_level_end_le)
        end.

        (* pull out S so we can rewrite about [firstn] *)
        rewrite Nat.sub_succ_l by solver.

        rewrite firstn_snoc with (d:=Datatypes.null_pointer)
          by (autorewrite with push_length; lia).
        rewrite fold_left_app.
        cbn [fold_left].
        cbv [nth_default_oobe Assumptions.Datatypes.ptable_pointer_oobe oob_value].

        (* fix up the nth_default thing *)
        rewrite nth_default_skipn.
        rewrite nth_default_firstn_low by solver.
        match goal with |- context [?a - ?b + ?b] =>
                        replace (a - b + b) with a by omega end.

        (* swap out starting concrete state for current one *)
        match goal with
          |- represents (abstract_reassign_pointer _ ?conc _ _ _ _) (reassign_pointer ?c _ _) =>
          rewrite abstract_reassign_pointer_change_concrete with (conc':=c)
            by
              repeat match goal with
                     | H : Forall _ _ |- _ => rewrite Forall_forall in H; apply H
                     | _ => apply In_nth_default_skipn_firstn
                     | _ => solver
                     end
        end.

        apply reassign_pointer_represents with (level := root_level - 1).
        { assumption. }
        { apply has_uniform_attrs_reassign_pointer;
            [ solve [auto using mm_map_level_noncircular] | ].
          match goal with
          | H : is_begin_or_block_start _ _ _ |- _ =>
            destruct H as [H | H];
              [ | replace root_level with (S (root_level - 1)) in H by solver ]
          end.
          { (* begin = n *)
            simplify.
            auto using mm_map_level_table_attrs. }
          { eapply has_uniform_attrs_expand_range; try eassumption; [ ].
            apply mm_map_level_table_attrs. } } } }
    { (* invariant holds at start *)
      right. simplify.
      {  lia. }
      {  erewrite mm_level_end_root_eq by eauto; apply mm_level_end_le. }
      {  cbv [is_begin_or_block_start]; solver. }
      { apply Forall_forall; intros.
        apply Forall_forall; intros.
        reflexivity. }
      { rewrite Nat.sub_diag.
        autorewrite with push_firstn push_fold_left.
        auto. } }
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

      (* get rid of all but 2 goals *)
      all:simplify.
      all:try apply N.to_nat_ltb.
      all:try apply Bool.negb_true_iff.
      all:simplify.
      all:try solve [rewrite ?Nnat.N2Nat.inj_sub; solver].

      { admit. (* TODO: assume this about mm_start_of_next_block, that its results are > input *) }
      {
        match goal with |- context [while_loop _ _ ?body] => remember body as F end.
        match goal with
        | H : represents (fold_left ?f ?ls ?a) ?x
          |- represents (fold_left ?f ?ls2 ?a) ?x =>
          assert (ls = ls2); [clear H | solver ]
        end.
        (* prove lists are equal (i.e. the table index gets to the end of the list) *)

        remember (snd (fst (fst (while_loop (fun '(_, begin0, _, _, _) => (begin0 <? end_)%N) (conc, begin, mm_index begin root_level, false, ppool) F)))) as IDX.
        remember (snd (fst (fst (fst (while_loop (fun '(_, begin0, _, _, _) => (begin0 <? end_)%N) (conc, begin, mm_index begin root_level, false, ppool) F))))) as BEGIN.
        remember (fst (fst (fst (fst (while_loop (fun '(_, begin0, _, _, _) => (begin0 <? end_)%N) (conc, begin, mm_index begin root_level, false, ppool) F))))) as CONC.
        clear HeqBEGIN HeqCONC HeqIDX.

        subst IDX.
        
        apply firstn_all2.
        autorewrite with push_length.
        rewrite Min.min_l by lia.
        match goal with 
        | H : (_ <? _)%N = false |- _ =>
          apply N.ltb_ge in H;
            apply mm_index_le_mono with (level:=root_level) in H; try solver
        end.
        assert (mm_index begin root_level <= mm_index end_ root_level) by admit.
        apply Nat.sub_le_mono_r.
        solver.
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
