Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.Lists.List.
Require Import Hafnium.AbstractModel.
Require Import Hafnium.Concrete.State.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Notations.
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

  (* if the new table is the same as the old, abstract state doesn't change *)
  Lemma reassign_pointer_noop_represents conc ptr t abst :
    represents abst conc ->
    conc.(ptable_deref) ptr = t ->
    represents abst (conc.(reassign_pointer) ptr t).
  Proof.
    repeat match goal with
           | _ => progress basics
           | _ => progress cbn [reassign_pointer ptable_deref]
           | _ => break_match
           | _ => solver
           | _ => apply represents_proper with (conc:=conc); eauto; [ ]
           end.
  Qed.

  (* given a sequence of page table indices, says whether the address is found
     under the same sequence of page table indexing *)
  Definition is_under_path (indices : list nat) (addr : uintpaddr_t) : bool :=
    forallb
      (fun '(lvl, i) => get_index lvl addr =? i)
      (combine (seq 0 4) indices).

  (* We haven't formalized anywhere that pointers don't repeat, so we return a
     list of all locations where the provided pointer exists even though we
     expect there is only one. *)
  Fixpoint index_sequences_to_pointer' (ptable_deref : ptable_pointer -> mm_page_table)
           (ptr : ptable_pointer) (root : ptable_pointer) (lvls_to_go : nat)
    : list (list nat) :=
    match lvls_to_go with
    | 0 => nil
    | S lvls_to_go' =>
      let lvl := 4 - lvls_to_go in
      if ptable_pointer_eq_dec root ptr
      then cons nil nil
      else
        flat_map
          (fun index =>
             let ptable := ptable_deref root in
             match get_entry ptable index with
             | Some pte =>
               if arch_mm_pte_is_table pte lvl
               then
                 let next_root :=
                     ptable_pointer_from_address
                       (arch_mm_table_from_pte pte lvl) in
                 map
                   (cons index)
                   (index_sequences_to_pointer'
                      ptable_deref ptr next_root lvls_to_go')
               else nil
             | None => nil
             end)
          (seq 0 MM_PTE_PER_PAGE)
    end.
  Definition index_sequences_to_pointer (ptable_deref : ptable_pointer -> mm_page_table)
             (ptr : ptable_pointer) (root : ptable_pointer) : list (list nat) :=
    index_sequences_to_pointer' ptable_deref ptr root 4.

  Definition abstract_reassign_pointer_for_entity
             (abst : abstract_state) (conc : concrete_state)
             (ptr : ptable_pointer) (owned valid : bool)
             (e : entity_id) (root_ptable : ptable_pointer)
    : abstract_state :=
    let paths := index_sequences_to_pointer
                   conc.(ptable_deref) ptr root_ptable in
    let under_pointer : uintpaddr_t -> bool :=
        fun addr =>
          existsb (fun p => is_under_path p addr) paths in
    let eq_dec := @entity_id_eq_dec _ Nat.eq_dec in
    {|
      accessible_by :=
        (fun a =>
           if (valid && under_pointer (pa_addr a))%bool
           then nodup eq_dec (e :: abst.(accessible_by) a)
           else remove eq_dec e (abst.(accessible_by) a));
      owned_by :=
        (fun a =>
           if (owned && under_pointer (pa_addr a))%bool
           then e
           else
             if eq_dec e (abst.(owned_by) a)
             then inr hid (* TODO: make owned_by an [option] so that unowned
                             memory is representable *)
             else abst.(owned_by) a)
    |}.

  (* Update the abstract state to make everything under the given pointer have
     the provided new owned/valid bits. *)
  Definition abstract_reassign_pointer
             (abst : abstract_state) (conc : concrete_state)
             (ptr : ptable_pointer) (attrs : attributes) : abstract_state :=
    (* first, get the owned/valid bits *)
    let stage1_mode := arch_mm_stage1_attrs_to_mode attrs in
    let stage2_mode := arch_mm_stage2_attrs_to_mode attrs in
    let s1_owned := ((stage1_mode & MM_MODE_UNOWNED) != 0)%N in
    let s1_valid := ((stage1_mode & MM_MODE_INVALID) != 0)%N in
    let s2_owned := ((stage2_mode & MM_MODE_UNOWNED) != 0)%N in
    let s2_valid := ((stage2_mode & MM_MODE_INVALID) != 0)%N in

    (* update the state with regard to Hafnium *)
    let abst :=
        abstract_reassign_pointer_for_entity
          abst conc ptr s1_owned s1_valid (inr hid) hafnium_root_ptable in

    (* update the state with regard to each VM *)
    fold_right
      (fun (v : vm) (abst : abstract_state) =>
         abstract_reassign_pointer_for_entity
           abst conc ptr s2_owned s2_valid (inl v.(vm_id)) v.(vm_root_ptable))
      abst
      vms.

  Definition has_uniform_attrs
             (ptable_deref : ptable_pointer -> mm_page_table)
             (t : mm_page_table) (level : nat) (attrs : attributes) : Prop :=
    forall (a : uintpaddr_t) (pte : pte_t),
      page_lookup' ptable_deref a t (4 - level) = Some pte ->
      forall lvl, arch_mm_pte_attrs pte lvl = attrs.

  Lemma reassign_pointer_represents conc ptr t abst :
    represents abst conc ->
    forall attrs level,
      has_uniform_attrs conc.(ptable_deref) t level attrs ->
      represents (abstract_reassign_pointer abst conc ptr attrs)
                 (conc.(reassign_pointer) ptr t).
  Proof.
    cbv [reassign_pointer represents].
    cbv [is_valid].
    cbv [vm_page_valid haf_page_valid vm_page_owned haf_page_owned].
    cbn [ptable_deref].
    basics; try solver.
    (* 4 subgoals *)
  Admitted.
End Proofs.
