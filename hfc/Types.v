(*
 * Copyright 2020 Jieung Kim (jieungkim@google.com) 
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


(* This file is to defined macro values of Hafnium *) 

From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

(* for shift opeartors *)
From Coq Require Import
     Init.Nat.

From ExtLib Require Import
     RelDec
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

From ITree Require Import
     ITree ITreeFacts.

Import ITreeNotations.
Import Monads.

Require Import Lang.

Import LangNotations.

Require Import Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.
Require Import BitNat.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Local Open Scope N_scope.



(* Some operations *)
(* #define UINT64_C(x)  ((x) + (UINT64_MAX - UINT64_MAX)) *)
(* #define UINT64_MAX  0xffffffffffffffff [exact] *)

(* JIEUNG (TODO): It requires check that the value is in the range. and the value is well-typed. *)
(* JIEUNG (TODO): I also hope to use quantifiers in assume and guarantee. Otherwise, I think we need 
   another method to express invariants? *) 
Definition UINT64_C (val : N) := val.

Definition UINT32_C (val : N) := val.

(* XXX: There are some platform related constat values in the system. which are defined in [build/BUILD.dn].
   How can we define them in our system? 
 defines = [ 
    "HEAP_PAGES=${plat_heap_pages}",
    "MAX_CPUS=${plat_max_cpus}",
    "MAX_VMS=${plat_max_vms}",
    "LOG_LEVEL=${log_level}",
  ]
 *)

(* XXX: I first set them as dummy values *)
Definition HEAP_PAGES := 100000%N.
Definition MAX_CPUS := 32%N.
Definition MAX_VMS := 32%N.
Definition LOG_LEVEL := 10000%N.

(* From the definition in [inc/vmapi/hf/types.h:#define] 
#define HF_HYPERVISOR_VM_ID 0

/**
 * An offset to use when assigning VM IDs.
 * The offset is needed because VM ID 0 is reserved.
 */
#define HF_VM_ID_OFFSET 1

/**
 * The index and ID of the primary VM, which is responsible for scheduling.
 *
 * These are not equal because ID 0 is reserved for the hypervisor itself.
 * Primary VM therefore gets ID 1 and all other VMs come after that.
 */
#define HF_PRIMARY_VM_INDEX 0
#define HF_PRIMARY_VM_ID (HF_VM_ID_OFFSET + HF_PRIMARY_VM_INDEX)
...
*)

Definition HF_VM_ID_OFFSET := 1%N.
Definition HF_PRIMARY_VM_INDEX := 0%N.
Definition HF_PRIMARY_VM_ID := (HF_VM_ID_OFFSET + HF_PRIMARY_VM_INDEX)%N.

(* From the definition in [src/arch/aarch64/inc/hf/arch/types.h] 
#define PAGE_LEVEL_BITS 9 
#define PAGE_BITS 12
#define STACK_ALIGN 16
#define FLOAT_REG_BYTES 16
#define NUM_GP_REGS 31
...
*)

Definition PAGE_LEVEL_BITS := 9%N.
Definition PAGE_BITS := 12%N.
Definition STACK_ALIGN := 16%N.
Definition FLOAT_REG_BYTES := 16%N.
Definition NUM_GP_REGS := 31%N.


(* typedef uint64_t pte_t; *)

Definition sizeof_pte_t := 8%N.

(* From the definition in [inc/hf/mm.h]
#define PAGE_SIZE (1 << PAGE_BITS)
...
*)
Definition MM_FLAG_STAGE1 := 4.
Definition PAGE_SIZE := N.shiftl 1 PAGE_BITS.

(*
/* The following are arch-independent page mapping modes. */
#define MM_MODE_R UINT32_C(0x0001) /* read */
#define MM_MODE_W UINT32_C(0x0002) /* write */
#define MM_MODE_X UINT32_C(0x0004) /* execute */
#define MM_MODE_D UINT32_C(0x0008) /* device */
 *)
Definition MM_MODE_R := 1%N.
Definition MM_MODE_W := 2%N. 
Definition MM_MODE_X := 4%N.
Definition MM_MODE_D := 8%N.

(*
#define MM_PTE_PER_PAGE (PAGE_SIZE / sizeof(pte_t))
*)

Definition MM_PTE_PER_PAGE := (PAGE_SIZE / sizeof_pte_t)%N. (* 512 *)
 
(* From the definition in [inc/hf/mm.h]
#define MM_MODE_INVALID UINT32_C(0x0010)
#define MM_MODE_UNOWNED UINT32_C(0x0020)
#define MM_MODE_SHARED  UINT32_C(0x0040)

(* #define MM_MODE_UNMAPPED_MASK (MM_MODE_INVALID | MM_MODE_UNOWNED) *)
 
#define MM_FLAG_COMMIT  0x01
#define MM_FLAG_UNMAP   0x02
#define MM_FLAG_STAGE1  0x04

*)

(* JIEUNG: FIXED -- coercion is not working very well in here. We need to fix that *)
Definition MM_MODE_UNOWNED := UINT32_C 16.
Definition MM_MODE_INVALID := UINT32_C 32.
Definition MM_MODE_SHARED := UINT32_C 64.

Definition MM_MODE_UNMAPPED_MASK := 48%N.


Definition MM_FLAG_COMMIT := 1%N.
Definition MM_FLAG_UNMAP := 2%N.

(* I manually calculate the result. I may need some way? *)





