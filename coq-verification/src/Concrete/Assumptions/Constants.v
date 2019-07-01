Require Import Coq.Lists.List.
Import ListNotations.

(*** This file lists the types and names of constants that we assume are defined
     in e.g. mm.h. These are left abstract because none of the proofs should
     depend on their exact values. ***)

(* PAGE_SIZE is a natural number *)
Axiom PAGE_SIZE : nat.

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
