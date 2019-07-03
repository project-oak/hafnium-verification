Require Import Coq.Lists.List.
Import ListNotations.

(*** This file lists the types and names of constants that we assume are defined
     in e.g. mm.h. These are left abstract because none of the proofs should
     depend on their exact values. ***)

(* page size parameters are natural numbers *)
Axiom PAGE_SIZE PAGE_BITS PAGE_LEVEL_BITS : nat.

(* PTEs per page -- natural number *)
Axiom MM_PTE_PER_PAGE : nat.

(* mm_mode flags are all natural numbers*)
(* N.B. : mode flags are taken as *indices* in the binary number; this makes it
   easier to state that they are all distinct and makes it true by construction
   that they each affect only one bit of the overall mode. *)
Axiom MM_MODE_R MM_MODE_W MM_MODE_X MM_MODE_INVALID MM_MODE_UNOWNED
      MM_MODE_SHARED : nat.

(* assume that all mode-flag indices are distinct from each other *)
Axiom mm_modes_distinct :
  NoDup [MM_MODE_R; MM_MODE_W; MM_MODE_X; MM_MODE_INVALID; MM_MODE_UNOWNED;
           MM_MODE_SHARED].

(* mm flags are all natural numbers*)
(* N.B. : In the same way as mm_mode flags, these are not binary numbers with
   a single bit set but rather represent the index of the bit that would be set,
   so that the single-bit-set format of the number is obvious by construction. *)
Axiom MM_FLAG_STAGE1 : nat.
