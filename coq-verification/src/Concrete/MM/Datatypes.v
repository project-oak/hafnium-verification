Require Import Hafnium.Concrete.Datatypes.
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
