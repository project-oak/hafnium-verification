Require Import Coq.Lists.List.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.ArchMM.
Require Import Hafnium.Concrete.Assumptions.Constants.
Require Import Hafnium.Concrete.Assumptions.Datatypes.
Require Import Hafnium.Concrete.MM.Datatypes.

(*** This file encodes in Coq how we expect page table lookups to work. It should
     be considered part of the TCB, because the proofs rely on this transcription
     being a correct description of the lookup procedure. ***)

(* index in root-level page table *)
Axiom index0 : uintpaddr_t -> nat.

(* index in the other 3 levels of page table *)
Axiom index1 : uintpaddr_t -> nat.
Axiom index2 : uintpaddr_t -> nat.
Axiom index3 : uintpaddr_t -> nat.

(* in-page offset *)
Axiom offset : uintpaddr_t -> nat.

(* if we have a table PTE, we want to extract the address and get a
   ptable_pointer out of it *)
Axiom ptable_pointer_from_address : paddr_t -> ptable_pointer.

Axiom page_table_size :
  forall ptable : mm_page_table, length ptable.(entries) = MM_PTE_PER_PAGE.

Definition get_entry (ptable : mm_page_table) (i : nat) : option pte_t :=
  nth_error ptable.(entries) i.

Definition get_index (level : nat) (a : uintpaddr_t) : nat :=
  match level with
  | 0 => index0 a
  | 1 => index1 a
  | 2 => index2 a
  | 3 => index3 a
  | _ => 0 (* invalid level *)
  end.

(* N.B. the [option] here doesn't mean whether the entry is
   valid/present; rather, the lookup should return [Some] for any
   valid input, but the PTE returned might be absent or invalid. *)
Fixpoint page_lookup'
         (ptable_deref : ptable_pointer -> mm_page_table)
         (a : uintpaddr_t)
         (ptr : ptable_pointer)
         (* encode the level as (4 - level), so Coq knows this terminates *)
         (lvls_to_go : nat)
  : option pte_t :=
  match lvls_to_go with
  | 0 => None
  | S lvls_to_go' =>
    let lvl := 4 - lvls_to_go in
    let ptable := ptable_deref ptr in
    match (get_entry ptable (get_index lvl a)) with
    | Some pte =>
      if (arch_mm_pte_is_table pte lvl)
      then
        (* follow the pointer to the next table *)
        let next_ptr := ptable_pointer_from_address
                          (arch_mm_table_from_pte pte lvl) in
           page_lookup' ptable_deref a next_ptr lvls_to_go'
      else Some pte
    | None => None
    end
  end.

Definition page_lookup
           (ptable_deref : ptable_pointer -> mm_page_table)
           (root_ptable : ptable_pointer)
           (a : uintpaddr_t) : option pte_t :=
  page_lookup' ptable_deref a root_ptable 4.
