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

Require Import Hafnium.Util.List.

(*** This file is for datatypes that are left abstract so as to avoid making any
     assumptions about their content. It may be necessary to instantiate these
     types later. ***)

(* pointers to page tables *)
Axiom ptable_pointer : Type.

(* equality between pointers is decidable *)
Axiom ptable_pointer_eq_dec :
  forall ptr1 ptr2 : ptable_pointer, {ptr1 = ptr2} + {ptr1 <> ptr2}.

(* assume NULL exists *)
Axiom null_pointer : ptable_pointer.

(* out-of-bounds accesses to lists of ptable_pointers return null_pointer *)
Global Instance ptable_pointer_oobe : OutOfBoundsElement ptable_pointer :=
  {| oob_value := null_pointer |}.
