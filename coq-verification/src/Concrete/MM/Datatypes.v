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

(*
  Some of the code in mm.c looks like this:

       struct mm_page_table *table;
       table = &mm_page_table_from_pa(t->root)[mm_index(begin, root_level)];

  The code directly indexes into an mm_page_table struct. Since #pragma is set,
  the struct won't be padded, so indexing returns a pointer to the given
  location in the [entries] list, and then this is treated as an mm_page_table
  pointer  Since the [entries] list is a fixed size, the new table will contain
  whatever locations in memory happen to exist after [entries] finishes. This
  unsafe access is protected against in the code by manual checks that the range
  of locations being accessed doesn't go past the end of the original table.

  For verification purposes, I have encoded this functionality as a function
  that takes an index and a page table and returns a page table with opaque
  entries after the given index (meaning proofs don't have any information
  about these entries and can't rely on any of their properties). This should
  capture the concept that although those entries are theoretically part of the
  page table, their contents are completely undefined.

  Depending on what kind of code semantics are eventually used for verification,
  the C code might need to change to do something less magical.
 *)

(* opaque type of PTEs returned by an out-of-bounds access *)
Axiom out_of_bounds_access_pte : pte_t.

Definition index_into_mm_page_table_struct (table : mm_page_table) (i : nat)
  : mm_page_table :=
  {| entries := skipn i table.(entries) ++ repeat out_of_bounds_access_pte i |}.

Notation "x {{ y }}" := (index_into_mm_page_table_struct x y) (at level 199, only parsing).

(* separate notation for getting the PTE at an index *)
Notation "x [[ y ]]" :=
  (nth_default out_of_bounds_access_pte x.(entries) y) (at level 199, only parsing).
