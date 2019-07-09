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
(* N.B. although the comment above [mpool_alloc] says it allocates an *entry*,
   the pointer it returns is immediately cast to an [mm_page_table], so it seems
   like it actually allocates full pages at a time (assuming a table takes one
   page of memory). Similarly, [mpool_free] frees one table-sized (= page-sized)
   block of memory at a time. *)
Axiom mpool_alloc : mpool -> option (mpool * ptable_pointer).

(* Return the new state of the mpool *)
Axiom mpool_free : mpool -> ptable_pointer -> mpool.

(* allocate contiguous locations -- the second argument is the number of tables
   to allocate *)
Axiom mpool_alloc_contiguous :
  mpool -> size_t -> size_t -> option (mpool * list ptable_pointer).
