Require Import Coq.NArith.BinNat.

(*** This file details how to represent some of the types in the source code
     using Coq types. ***)

(* an absolute address is represented by a natural number *)
Definition uintpaddr_t : Type := nat.

(* a size is represented by a natural number *)
Definition size_t : Type := nat.

(* an int is represented by a *binary* natural number *)
Definition int := N.

(* attributes (uint64_t) are represented by a binary natural number*)
Definition attributes := N.

(* a page table entry (uint64_t) is represented by a binary natural number *)
Definition pte_t := N.
