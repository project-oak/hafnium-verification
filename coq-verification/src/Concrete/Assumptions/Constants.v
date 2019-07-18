Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNat.
Import ListNotations.

(*** This file lists the types and names of constants that we assume are defined
     in e.g. mm.h. These are left abstract because none of the proofs should
     depend on their exact values. ***)

(* page size parameters are natural numbers *)
Axiom PAGE_SIZE PAGE_BITS PAGE_LEVEL_BITS : nat.

(* PTEs per page -- natural number *)
Axiom MM_PTE_PER_PAGE : nat.

(* A lot of constants are MM_FLAG or MM_MODE and are single bits designed to be
   or-ed with binary numbers to create flag or mode codes. Proofs should not
   depend on where the bit is located (as long as it is distinct from the others
   and within the number of bits in the flag/mode code), so we want to leave these
   indices as assumptions instead of hardcoding their values. However, we still
   want to be able to prove that they are in fact single-bit numbers.
   Compromising between these constraints, we assume a natural number for each
   flag/mode that represents the *index* of the set bit, and write a definition
   that converts them to binary numbers. *)
Axiom MM_MODE_R_index MM_MODE_W_index MM_MODE_X_index MM_MODE_INVALID_index
      MM_MODE_UNOWNED_index MM_MODE_SHARED_index : nat.
Axiom MM_FLAG_STAGE1_index MM_FLAG_COMMIT_index MM_FLAG_UNMAP_index : nat.

Definition index_to_N (i : nat) := N.shiftl 1 (N.of_nat i).

Definition MM_MODE_R : N := index_to_N MM_MODE_R_index.
Definition MM_MODE_W : N := index_to_N MM_MODE_W_index.
Definition MM_MODE_X : N := index_to_N MM_MODE_X_index.
Definition MM_MODE_INVALID : N := index_to_N MM_MODE_INVALID_index.
Definition MM_MODE_UNOWNED : N := index_to_N MM_MODE_UNOWNED_index.
Definition MM_MODE_SHARED : N := index_to_N MM_MODE_SHARED_index.
Definition MM_FLAG_STAGE1 : N := index_to_N MM_FLAG_STAGE1_index.
Definition MM_FLAG_COMMIT : N := index_to_N MM_FLAG_COMMIT_index.
Definition MM_FLAG_UNMAP : N := index_to_N MM_FLAG_UNMAP_index.

(* assume that all indices are distinct from each other *)
Axiom mm_modes_distinct :
  NoDup [MM_MODE_R_index; MM_MODE_W_index; MM_MODE_X_index; MM_MODE_INVALID_index;
           MM_MODE_UNOWNED_index; MM_MODE_SHARED_index].
Axiom mm_flags_distinct :
  NoDup [MM_FLAG_STAGE1_index; MM_FLAG_COMMIT_index].

(* assume that PAGE_BITS is positive *)
Axiom PAGE_BITS_pos : 0 < PAGE_BITS.
