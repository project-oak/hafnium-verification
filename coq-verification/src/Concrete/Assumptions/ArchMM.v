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

Require Import Coq.NArith.BinNat.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Constants.
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


(* Assumptions about the properties of arch/mm.c *)
Axiom stage1_root_table_count_ok : arch_mm_stage1_root_table_count < Nat.pow 2 PAGE_LEVEL_BITS.
Axiom stage2_root_table_count_ok : arch_mm_stage2_root_table_count < Nat.pow 2 PAGE_LEVEL_BITS.
Axiom stage1_max_level_pos : 0 < arch_mm_stage1_max_level.
Axiom stage2_max_level_pos : 0 < arch_mm_stage2_max_level.

(* absent and block PTEs are not tables *)
Axiom absent_not_table :
  forall level,
    arch_mm_pte_is_table (arch_mm_absent_pte level) level = false.
Axiom block_not_table :
  forall level pa attrs,
    arch_mm_pte_is_table (arch_mm_block_pte level pa attrs) level = false.

(* shorthand definitions just for this file to make axiom statements neater *)
Local Notation get_bit n bit := (negb (N.eqb (N.land n bit) 0)). (* (n & bit) != 0 *)

(* arch_mm_pte_is_valid is true iff [ attrs & PTE_VALID != 0 ] *)
Axiom is_valid_matches_flag :
  forall pte level,
    let attrs := arch_mm_pte_attrs pte level in
    arch_mm_pte_is_valid pte level = get_bit attrs PTE_VALID.

(* arch_mm_pte_is_present returns true iff the valid bit is 0 or the stage-2
   owned bit is true *)
Axiom is_present_iff :
  forall pte level,
    let attrs := arch_mm_pte_attrs pte level in
    let mode := arch_mm_stage2_attrs_to_mode attrs in
    arch_mm_pte_is_present pte level =
    (get_bit attrs PTE_VALID || get_bit mode MM_MODE_UNOWNED)%bool.

(* when attributes are converted to a stage-2 mode, the valid bit matches *)
Axiom stage2_attrs_to_mode_valid :
  forall attrs,
    ((N.land attrs PTE_VALID) =? 0)%N =
    get_bit (arch_mm_stage2_attrs_to_mode attrs) MM_MODE_INVALID.

(* absent PTEs don't have the valid bit set *)
Axiom absent_invalid :
  forall level, arch_mm_pte_is_valid (arch_mm_absent_pte level) level = false.

(* we assume there exists some set of attributes that we can use which is neither
   valid nor stage-2 owned *)
Axiom absent_attrs : attributes.
Axiom absent_attrs_invalid : get_bit absent_attrs PTE_VALID = false.
Axiom absent_attrs_unowned :
  get_bit (arch_mm_stage2_attrs_to_mode absent_attrs) MM_MODE_UNOWNED = true.
