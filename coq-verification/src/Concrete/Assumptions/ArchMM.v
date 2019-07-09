Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Addr.

(*** This file defines (the necessary parts of) the API provided by arch/mm.h,
     which is assumed correct for now. In order to replace this assumption with
     a proof of correctness, replace the [Axiom]s with definitions and proofs,
     leaving their types the same. ***)

(* levels are represented by natural numbers, but just to make it
   extra clear we give them an alias to differentiate them from
   other [nat]s *)
Local Notation level := nat.

Axiom arch_mm_absent_pte : level -> pte_t.

Axiom arch_mm_block_pte : level -> paddr_t -> attributes -> pte_t.

(* N.B. we take in a ptable_pointer instead of a paddr_t here *)
Axiom arch_mm_table_pte : level -> ptable_pointer -> pte_t.

Axiom arch_mm_pte_is_present : pte_t -> level -> bool.

Axiom arch_mm_pte_is_valid : pte_t -> level -> bool.

Axiom arch_mm_pte_is_block : pte_t -> level -> bool.

Axiom arch_mm_pte_is_table : pte_t -> level -> bool.

Axiom arch_mm_table_from_pte : pte_t -> level -> paddr_t.

Axiom arch_mm_pte_attrs : pte_t -> level -> attributes.

Axiom arch_mm_stage2_attrs_to_mode : attributes -> mode_t.

Axiom arch_mm_stage1_attrs_to_mode : attributes -> mode_t.

Axiom arch_mm_stage2_max_level : level.

Axiom arch_mm_stage1_max_level : level.

Axiom arch_mm_stage2_root_table_count : nat.

Axiom arch_mm_stage1_root_table_count : nat.

Axiom arch_mm_mode_to_stage1_attrs : mode_t -> attributes.

Axiom arch_mm_mode_to_stage2_attrs : mode_t -> attributes.

Axiom arch_mm_clear_pa : paddr_t -> paddr_t.

Axiom arch_mm_is_block_allowed : level -> bool.

Axiom arch_mm_block_from_pte : pte_t -> level -> paddr_t.

Axiom arch_mm_combine_table_entry_attrs : attributes -> attributes -> attributes.
