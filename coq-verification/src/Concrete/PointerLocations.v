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
Require Import Coq.NArith.BinNat.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Parameters.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.ArchMM.
Require Import Hafnium.Concrete.Assumptions.Constants.
Require Import Hafnium.Concrete.Assumptions.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Mpool.
Require Import Hafnium.Concrete.Assumptions.PageTables.
Require Import Hafnium.Concrete.MM.Datatypes.
Require Import Hafnium.Util.List.
Require Import Hafnium.Util.Tactics.

(* TODO : find a different place for this section? *)
Section AddressMatchesIndices.
  Definition address_matches_indices_alt stage a idxs : Prop :=
    firstn (length idxs)
           (rev
              (map (fun lvl => get_index stage lvl a)
                   (seq 0 (S (S (max_level stage)))))) =
    firstn (S (S (max_level stage))) idxs.
  Definition address_matches_indices stage a idxs : Prop :=
    (forall i d,
        i < length idxs ->
        i < S (S (max_level stage)) ->
        get_index stage (max_level stage + 1 - i) a = nth i idxs d).

  Lemma address_matches_indices_alt_equiv stage a idxs :
    address_matches_indices_alt stage a idxs <-> address_matches_indices stage a idxs.
  Proof.
    cbv [address_matches_indices address_matches_indices_alt]. basics.
    rewrite <-map_rev, <-map_firstn.
    rewrite <-nth_eq_iff by (try apply Nat.eq_dec; exists 0; exists 1; solver).
    split; basics;
      [ destruct (Compare_dec.lt_dec i (S (S (max_level stage))))
      | destruct (Compare_dec.lt_dec n (Nat.min (length idxs) (S (S (max_level stage))))) ];
      repeat match goal with
             | _ => progress basics
             | _ => progress autorewrite with push_length
             | _ => rewrite nth_default_eq in *
             | H : context [_ = nth _ _ _] |- _ =>
               rewrite <-H by solver;
                 erewrite nth_indep by (autorewrite with push_length; solver)
             | H : context [_ = nth _ _ _] |- _ =>
               erewrite nth_indep by solver;
                 rewrite <-nth_firstn with (i0 := (S (S (max_level stage)))) by solver;
                 rewrite <-H
             | _ => rewrite nth_overflow by (autorewrite with push_length; solver)
             | _ => rewrite map_nth with (d:=0) by solver
             | _ => rewrite nth_firstn by solver
             | _ => rewrite rev_nth by (autorewrite with push_length; solver)
             | _ => rewrite seq_nth by solver
             | |- _ <-> _ => split
             | _ => solver
             | _ => f_equal; solver
             end.
  Qed.

  Definition address_matches_indices_alt_dec stage a idxs :
    {address_matches_indices_alt stage a idxs} + {~ address_matches_indices_alt stage a idxs}.
  Proof.
    cbv [address_matches_indices_alt].
    apply list_eq_dec, Nat.eq_dec.
  Defined.

  Definition address_matches_indices_dec stage a idxs :
    {address_matches_indices stage a idxs} + {~ address_matches_indices stage a idxs}.
  Proof.
    destruct (address_matches_indices_alt_dec stage a idxs); basics;
    rewrite address_matches_indices_alt_equiv in *; solver.
  Defined.

  Definition address_matches_indices_decidable stage a idxs :
    Decidable.decidable (address_matches_indices stage a idxs).
  Proof.
    cbv [Decidable.decidable].
    destruct (address_matches_indices_alt_dec stage a idxs); basics;
      rewrite address_matches_indices_alt_equiv in *; solver.
  Defined.
End AddressMatchesIndices.

Section LevelFromIndices.
  Definition level_from_indices stage (idxs : list nat) : nat :=
    max_level stage + 2 - length idxs.
End LevelFromIndices.

Section PointerLocations.
  Context (deref : ptable_pointer -> mm_page_table).

  (* We haven't formalized anywhere that pointers don't repeat, so we return a
     list of all locations where the provided pointer exists even though we
     expect there is only one. *)
  (* N.B. level is the level above the one we're looking at (this is so 0 can be
     the base case) *)
  Fixpoint index_sequences_to_pointer''
           (ptr : ptable_pointer) (root : ptable_pointer) (level : nat)
    : list (list nat) :=
    match level with
    | 0 => nil
    | S level' =>
      if ptable_pointer_eq_dec root ptr
      then cons nil nil
      else
        let ptable := deref root in
        flat_map
          (fun index =>
             match get_entry ptable index with
             | Some pte =>
               if arch_mm_pte_is_table pte level'
               then
                 let next_root :=
                     ptable_pointer_from_address
                       (arch_mm_table_from_pte pte level') in
                 map
                   (cons index)
                   (index_sequences_to_pointer'' ptr next_root level')
               else nil
             | None => nil
             end)
          (seq 0 (length ptable.(entries)))
    end.
  Fixpoint index_sequences_to_pointer'
           (ptr : ptable_pointer) (root_index : nat)
           (root_ptrs : list ptable_pointer) (stage : Stage) : list (list nat) :=
    match root_ptrs with
    | nil => nil
    | cons root_ptr root_ptrs' =>
      (map (cons root_index)
           (index_sequences_to_pointer'' ptr root_ptr (max_level stage + 1)))
        ++ index_sequences_to_pointer' ptr (S root_index) root_ptrs' stage
    end.
  Definition index_sequences_to_pointer
           (ptr : ptable_pointer) (root_ptable : mm_ptable) (stage : Stage) :=
    index_sequences_to_pointer'
      ptr 0 (ptr_from_va (va_from_pa root_ptable.(root))) stage.

  Inductive pointer_location (ppool : mpool) : Type :=
  | table_loc : mm_ptable -> list nat -> pointer_location ppool
  | mpool_loc : pointer_location ppool
  .

  Definition pointer_location_eq_dec
             (ppool : mpool) (loc1 loc2 : pointer_location ppool)
    : { loc1 = loc2 } + { loc1 <> loc2 }.
  Proof.
    destruct loc1, loc2;
    repeat match goal with
           | p : mm_ptable |- _ => destruct p
           | r1 : paddr_t, r2 : paddr_t |- _ =>
             destruct (paddr_t_eq_dec r1 r2); [ subst | right; congruence ]
           | l1 : list nat, l2 : list nat |- _ =>
             destruct (list_eq_dec Nat.eq_dec l1 l2); [ subst | right; congruence ]
           | _ => right; congruence
           | _ => left; congruence
           end.
  Defined.

  (* This section includes some definitions which use information from the
     concrete parameters *)
  Section with_concrete_params.
    Context {cp : concrete_params}.

    Let vm_ptables := map vm_ptable vms.

    Inductive has_location {ppool : mpool}
      : ptable_pointer -> pointer_location ppool -> Prop :=
    | has_table_loc_stage1 :
        forall idxs ptr,
          In idxs (index_sequences_to_pointer ptr hafnium_ptable Stage1) ->
          has_location ptr (table_loc ppool hafnium_ptable idxs)
    | has_table_loc_stage2 :
        forall root_ptable idxs ptr,
          In root_ptable vm_ptables ->
          In idxs (index_sequences_to_pointer ptr root_ptable Stage2) ->
          has_location ptr (table_loc ppool root_ptable idxs)
    | has_mpool_loc :
        forall ptr,
          mpool_contains ppool ptr ->
          has_location ptr (mpool_loc ppool)
    .

    (* every ptable_pointer has at most one location *)
    Definition locations_exclusive (ppool : mpool) : Prop :=
      forall ptr loc1 loc2,
        @has_location ppool ptr loc1 -> @has_location ppool ptr loc2 -> loc1 = loc2.
  End with_concrete_params.


  Section Proofs.
    Lemma index_sequences_to_pointer''_root ptr level :
      0 < level ->
      In nil (index_sequences_to_pointer'' ptr ptr level).
    Proof.
      destruct level; [solver|]; intros.
      cbn [index_sequences_to_pointer''].
      break_match; solver.
    Qed.

    Lemma index_sequences_to_pointer'_nth_default root_list stage :
      forall i j k,
        i < length root_list ->
        k = i + j ->
        In (k :: nil)
           (index_sequences_to_pointer'
              (nth_default_oobe root_list i) j root_list stage).
    Proof.
      cbv [nth_default_oobe]. pose proof (max_level_pos stage).
      induction root_list; destruct i; cbn [length index_sequences_to_pointer'];
        repeat match goal with
               | _ => progress basics
               | _ => progress autorewrite with push_nth_default
               | _ => rewrite Nat.add_0_l
               | _ => apply in_or_app
               | _ => left; apply in_map, index_sequences_to_pointer''_root; solver
               | _ => right; apply IHroot_list; solver
               | _ => solver
               end.
    Qed.

    (* Helper lemma for [nth_error_index_sequences_root] *)
    Lemma nth_error_index_sequences_root' root_ptrs stage ptr :
      forall i root_index,
        nth_error root_ptrs i = Some ptr ->
        In (cons (root_index + i) nil)
           (index_sequences_to_pointer' ptr root_index root_ptrs stage).
    Proof.
      induction root_ptrs; [ intros *; rewrite nth_error_nil; solver | ].
      destruct i; cbn [nth_error index_sequences_to_pointer']; basics.
      { apply in_or_app; left. rewrite Nat.add_0_r. apply in_map.
        apply index_sequences_to_pointer''_root; solver. }
      { apply in_or_app; right. rewrite <-Nat.add_succ_comm.
        solver. }
    Qed.

    (* If you're searching for the index sequences leading to [ptr], and [ptr] is
     a pointer to the root page table at index [i] in the root table list, then
     the resulting index sequences will include (cons i nil).*)
    Lemma nth_error_index_sequences_root root_ptable i stage ptr :
      nth_error (ptr_from_va (va_from_pa (root root_ptable))) i = Some ptr ->
      In (cons i nil) (index_sequences_to_pointer ptr root_ptable stage).
    Proof.
      cbv [index_sequences_to_pointer]; intro Hnth.
      eapply nth_error_index_sequences_root' with (root_index:=0) in Hnth.
      rewrite Nat.add_0_l in Hnth. solver.
    Qed.

    Lemma index_sequences_not_nil' ptr root_ptrs stage :
      Exists (fun root_ptr =>
                index_sequences_to_pointer''
                  ptr root_ptr (max_level stage + 1) <> nil)
             root_ptrs ->
      forall root_index,
        index_sequences_to_pointer' ptr root_index root_ptrs stage <> nil.
    Proof.
      induction 1; cbn [index_sequences_to_pointer'];
        eauto using app_not_nil_l, app_not_nil_r, map_not_nil.
    Qed.

    Lemma index_sequences_not_nil ptr root_ptable stage :
      Exists (fun root_ptr =>
                index_sequences_to_pointer''
                  ptr root_ptr (max_level stage + 1) <> nil)
             (ptr_from_va (va_from_pa (root root_ptable))) ->
      index_sequences_to_pointer ptr root_ptable stage <> nil.
    Proof.
      cbv [index_sequences_to_pointer]. basics.
      apply index_sequences_not_nil'; eauto.
    Qed.

    Lemma get_entry_index_sequences level :
      forall i root_ptr e,
        0 < level ->
        get_entry (deref root_ptr) i = Some e ->
        arch_mm_pte_is_table e level = true ->
        index_sequences_to_pointer''
          (ptable_pointer_from_address (arch_mm_table_from_pte e level))
          root_ptr (S level) <> nil.
    Proof.
      basics; cbn [index_sequences_to_pointer''];
        match goal with
        | H : get_entry _ _ = Some _ |- _ =>
          pose proof H; cbv [get_entry] in H; apply nth_error_Some_range in H
        end;
        repeat match goal with
               | _ => progress basics
               | H : get_entry _ _ = Some _ |- _ => rewrite H
               | _ => break_match
               | _ => apply flat_map_not_nil with (a:=i)
               | _ => apply in_seq; solver
               | _ => solver
               | _ => solve [eauto using map_not_nil, In_not_nil,
                             index_sequences_to_pointer''_root]
               end.
    Qed.

    Lemma page_lookup'_proper deref2 level stage :
      forall root_ptr,
        (forall ptr,
            index_sequences_to_pointer'' ptr root_ptr level <> nil ->
            deref ptr = deref2 ptr) ->
        forall a,
          page_lookup' deref a (deref root_ptr) level stage
          = page_lookup' deref2 a (deref root_ptr) level stage.
    Proof.
      induction level; cbn [page_lookup'];
        [ | destruct (Nat.eq_dec level 0); [ basics; reflexivity | ] ];
        repeat match goal with
               | _ => progress basics
               | _ => break_match
               | H : _ |- _ =>
                 rewrite <-H; [ | eapply get_entry_index_sequences; solver ]
               | H : context [deref _ = deref2 _] |- _ => apply H
               | _ => apply IHlevel
               | _ => solver
               end.
      cbn [index_sequences_to_pointer''].
      break_match; [ solver | ].
      cbv [get_entry] in *.
      match goal with H : _ |- _ =>
                      pose proof H;
                        apply nth_error_Some_range in H
      end.
      match goal with H : context [get_index ?s ?l ?addr] |- _ =>
                      eapply flat_map_not_nil with (a0:=get_index s l addr);
                        [ apply in_seq; solver | ]
      end.
      repeat break_match; try solver; [ ].
      apply map_not_nil; solver.
    Qed.

    Lemma page_lookup_proper deref2 root_ptable stage :
      (forall ptr,
          index_sequences_to_pointer ptr root_ptable stage <> nil ->
          deref ptr = deref2 ptr) ->
      forall a,
        page_lookup deref root_ptable stage a = page_lookup deref2 root_ptable stage a.
    Proof.
      cbv [page_lookup];
        repeat match goal with
               | _ => progress basics
               | H : _ = Some _ |- _ =>
                 pose proof (nth_error_In _ _ H);
                   eapply nth_error_index_sequences_root in H;
                   [ | solver .. ]
               | H : context [deref _ = deref2 _] |- _ => rewrite <-H by solver
               | H : context [deref _ = deref2 _] |- _ =>
                 apply H; apply index_sequences_not_nil
               | _ => apply page_lookup'_proper
               | _ => rewrite Exists_exists
               | _ => break_match
               | _ => solver
               end.
    Qed.

    (* TODO: clean up WIP proofs, move definition of page_table_lookup elsewhere *)
    (*** The below proofs are a work in progress to connect index_sequences_to_pointer with page_lookup ***)

    Section PageTableLookup.
      (* TODO: remove if unused *)
      (* Look up the page table that corresponds to the given indices *)
      Fixpoint page_table_lookup' root_ptr (idxs : list nat) level : option ptable_pointer :=
        match idxs with
        | nil => Some root_ptr
        | cons i idxs' =>
          let table := deref root_ptr in
          match get_entry table i with
          | Some pte =>
            if arch_mm_pte_is_table pte level
            then
              let next_ptr := ptable_pointer_from_address (arch_mm_table_from_pte pte level) in
              page_table_lookup' next_ptr idxs' (level - 1)
            else Some root_ptr
          | None => None
          end
        end.
      Definition page_table_lookup root_ptable idxs stage : option ptable_pointer :=
        let root_tables := ptr_from_va (va_from_pa (root root_ptable)) in
        match idxs with
        | nil => None
        | cons i idxs' =>
          match nth_error root_tables i with
          | Some table_ptr => page_table_lookup' table_ptr idxs' (max_level stage)
          | None => None
          end
        end.
    End PageTableLookup.

    (* TODO: remove if unused *)
    Lemma page_table_lookup_equiv root_ptable idxs stage a ptr :
      address_matches_indices stage a idxs ->
      page_table_lookup root_ptable idxs stage = Some ptr ->
      page_lookup deref root_ptable stage a
      = page_lookup' deref a (deref ptr) (level_from_indices stage idxs) stage.
    Admitted.

    Section with_concrete_params.
      Context {cp : concrete_params}.

      Definition root_ptable_matches_stage root_ptable stage : Prop :=
        match stage with
        | Stage1 => root_ptable = hafnium_ptable
        | Stage2 => In root_ptable (map vm_ptable vms)
        end.

      Lemma has_location_index_sequence ppool ptr root_ptable idxs stage :
        root_ptable_matches_stage root_ptable stage ->
        ~ In hafnium_ptable (map vm_ptable vms) ->
        has_location ptr (table_loc ppool root_ptable idxs) ->
        In idxs (index_sequences_to_pointer ptr root_ptable stage).
      Proof.
        intros.
        match goal with H : context [has_location] |- _ =>
                        invert H end; destruct stage; try solver.
      Qed.

      Lemma index_sequences_has_location ppool root_ptable idxs ptr stage :
        root_ptable_matches_stage root_ptable stage ->
        In idxs (index_sequences_to_pointer ptr root_ptable stage) ->
        has_location ptr (table_loc ppool root_ptable idxs).
      Proof.
        destruct stage; cbv [root_ptable_matches_stage]; basics; constructor; solver.
      Qed.

      Lemma has_location_index_sequences_not_nil ppool root_ptable idxs ptr stage :
        has_location ptr (table_loc ppool root_ptable idxs) ->
        ~ In hafnium_ptable (map vm_ptable vms) ->
        root_ptable_matches_stage root_ptable stage ->
        index_sequences_to_pointer ptr root_ptable stage <> nil.
      Proof.
        basics.
        eapply In_not_nil; eapply has_location_index_sequence; solver.
      Qed.

      Lemma has_location_hd_index_sequences ppool root_ptable idxs ptr stage :
        has_location ptr (table_loc ppool root_ptable idxs) ->
        locations_exclusive ppool ->
        root_ptable_matches_stage root_ptable stage ->
        ~ In hafnium_ptable (map vm_ptable vms) ->
        hd nil (index_sequences_to_pointer ptr root_ptable stage) = idxs.
      Proof.
        basics.
        match goal with H : _ |- _ =>
                        eapply has_location_index_sequence in H; [ | solver .. ] end.
        match goal with H : In _ _ |- _ =>
                        pose proof (hd_in nil _ (In_not_nil _ _ H)) end.
        repeat match goal with
               | H : In _ _ |- _ =>
                 eapply index_sequences_has_location with (ppool:=ppool) in H;
                   [ | solver .. ]
               end.
        match goal with H : locations_exclusive _, H1 : _, H2 : _ |- _ =>
                        specialize (H _ _ _ H1 H2); invert H
        end.
        solver.
      Qed.

      Lemma index_sequences_to_pointer''_length ptr :
        forall level_above root_ptr idxs,
          In idxs (index_sequences_to_pointer'' ptr root_ptr level_above) ->
          length idxs < level_above.
      Proof.
        induction level_above; cbn [index_sequences_to_pointer''];
          repeat match goal with
                 | _ => progress basics
                 | _ => progress invert_list_properties
                 | _ => progress cbn [length]
                 | H : In _ (flat_map _ _) |- _ => apply in_flat_map in H
                 | H : In _ (map _ _) |- _ => apply in_map_iff in H
                 | H : In _ _ |- _ => apply IHlevel_above in H
                 | _ => break_match
                 | _ => solver
                 end.
      Qed.

      Lemma index_sequences_to_pointer'_length ptr stage :
        forall root_ptrs root_index idxs,
          In idxs (index_sequences_to_pointer' ptr root_index root_ptrs stage) ->
          length idxs <= S (max_level stage).
      Proof.
        induction root_ptrs; cbn [index_sequences_to_pointer'];
          basics; invert_list_properties; [ ].
        rewrite in_app_iff, in_map_iff in *; basics; cbn [length]; [ | solver ].
        match goal with H : _ |- _ =>
                        apply index_sequences_to_pointer''_length in H
        end; solver.
      Qed.

      Lemma index_sequences_to_pointer_length ptr root_ptable idxs stage :
        In idxs (index_sequences_to_pointer ptr root_ptable stage) ->
        length idxs <= S (max_level stage).
      Proof.
        cbv [index_sequences_to_pointer]; basics.
        eapply index_sequences_to_pointer'_length; solver.
      Qed.

      Lemma has_location_length ppool ptr root_ptable idxs stage :
        has_location ptr (table_loc ppool root_ptable idxs) ->
        root_ptable_matches_stage root_ptable stage ->
        ~ In hafnium_ptable (map vm_ptable vms) ->
        length idxs <= S (max_level stage).
      Proof.
        basics.
        eapply index_sequences_to_pointer_length.
        eapply has_location_index_sequence; solver.
      Qed.

      (* TODO: remove if unused *)
      Lemma has_location_step
            ppool root_ptable stage idxs ptr i level e :
        root_ptable_matches_stage root_ptable stage ->
        has_location ptr (table_loc ppool root_ptable idxs) ->
        level = level_from_indices stage idxs ->
        get_entry (deref ptr) i = Some e ->
        arch_mm_pte_is_table e level = true ->
        let next_ptr :=
            ptable_pointer_from_address (arch_mm_table_from_pte e level) in
        has_location next_ptr (table_loc ppool root_ptable (idxs ++ cons i nil)).
      Admitted.

      (* TODO: remove if unused *)
      Lemma has_location_table_lookup ppool ptr root_ptable idxs stage :
        has_location ptr (table_loc ppool root_ptable idxs) ->
        page_table_lookup root_ptable idxs stage = Some ptr.
      Admitted.

      (* TODO: remove if unused *)
      Lemma page_lookup_from_location root_ptable idxs ppool stage a ptr :
        has_location ptr (table_loc ppool root_ptable idxs) ->
        address_matches_indices stage a idxs ->
        page_lookup deref root_ptable stage a
        = page_lookup' deref a (deref ptr) (level_from_indices stage idxs) stage.
      Proof.
        intros;
          match goal with H : _ |- _ =>  eapply has_location_table_lookup in H end.
        eapply page_table_lookup_equiv; eauto.
      Qed.

      (* TODO: just guessing that this might come in handy; remove if unused *)
      Lemma table_locations_exclusive ppool ptr1 ptr2 root_ptable idxs :
        has_location ptr1 (table_loc ppool root_ptable idxs) ->
        has_location ptr2 (table_loc ppool root_ptable idxs) ->
        ptr1 = ptr2.
      Admitted.
    End with_concrete_params.
  End Proofs.
End PointerLocations.
