Require Import Coq.Lists.List.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Util.List.
Require Import Hafnium.Concrete.Assumptions.Addr.

(*** This file transcribes some datatypes found in mm.h, with original C in
     comments alongside ***)

(*
struct mm_page_table {
	alignas(PAGE_SIZE) pte_t entries[MM_PTE_PER_PAGE];
};
 *)
Record mm_page_table := { entries : list pte_t }.

(*
struct mm_ptable {
	/** Address of the root of the page table. */
	paddr_t root;
};
 *)
Record mm_ptable := { root : paddr_t }.

(* Shortcut definition for replacing the PTE at a given index *)
Definition mm_page_table_replace_entry
           (t : mm_page_table) (pte : pte_t) (index : nat) : mm_page_table :=
  {| entries := set_nth t.(entries) pte index |}.

(* opaque type of PTEs returned by an out-of-bounds access *)
Axiom out_of_bounds_access_pte : pte_t.

(* out-of-bounds accesses to lists of PTEs return out_of_bounds_access_pte *)
Global Instance ptable_pointer_oobe : OutOfBoundsElement pte_t :=
  {| oob_value := out_of_bounds_access_pte |}.
