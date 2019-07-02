Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Datatypes.

(*** This file defines (the necessary parts of) the API provided by mpool.h,
     which is assumed correct for now. In order to replace this assumption with
     a proof of correctness, replace the [Axiom]s with definitions and proofs,
     leaving their types the same. ***)

Axiom mpool : Type.

Axiom mpool_init_with_fallback : mpool -> mpool.

(* If there is a fallback, return its new state, otherwise return [None] *)
Axiom mpool_fini : mpool -> option mpool.

(* If there's a location available, return the new state and the pointer,
   otherwise return [None] *)
Axiom mpool_alloc : mpool -> option (mpool * ptable_pointer).

(* Return the new state of the mpool *)
Axiom mpool_free : mpool -> ptable_pointer -> mpool.

(* TODO: add axioms for correctness properties, as needed *)
