Require Import Coq.NArith.BinNat.
Require Import Coq.Lists.List.

(*** This file details how to represent some of the types in the source code
     using Coq types. ***)

(* absolute addresses are represented by binary natural numbers *)
Definition uintpaddr_t : Type := N.
Definition uintvaddr_t : Type := N.

(* a size is represented by a natural number *)
Definition size_t : Type := nat.

(* an int is represented by a *binary* natural number *)
Definition int := N.

(* attributes (uint64_t) are represented by a binary natural number*)
Definition attributes := N.

(* memory modes (int) are represented by binary natural numbers *)
Definition mode_t := N.

(* a page table entry (uint64_t) is represented by a binary natural number *)
Definition pte_t := N.

(* page tables are a list of PTEs *)
Definition page_table := list pte_t.

(* hf_share enum *)
Inductive hf_share :=
| HF_MEMORY_GIVE
| HF_MEMORY_LEND
| HF_MEMORY_SHARE
| INVALID
.
