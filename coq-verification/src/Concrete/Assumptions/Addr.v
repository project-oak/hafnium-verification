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

(*** This file defines (the necessary parts of) the API provided by addr.h,
     which is assumed correct for now. In order to replace this assumption with
     a proof of correctness, replace the [Axiom]s with definitions and proofs,
     leaving their types the same. ***)

Axiom ipaddr_t : Type.

Axiom paddr_t : Type.

Axiom vaddr_t : Type.

Axiom pa_init : uintpaddr_t -> paddr_t.

Axiom pa_addr : paddr_t -> uintpaddr_t.

Axiom pa_difference : paddr_t -> paddr_t -> size_t.

Axiom ipa_addr : ipaddr_t -> uintpaddr_t.

Axiom va_init : uintvaddr_t -> vaddr_t.

Axiom ipa_add : ipaddr_t -> size_t -> ipaddr_t.

Axiom va_addr : vaddr_t -> uintvaddr_t.

Axiom va_from_pa : paddr_t -> vaddr_t.

Axiom pa_from_va : vaddr_t -> paddr_t.

Axiom pa_from_ipa : ipaddr_t -> paddr_t.

Axiom ptr_from_va : vaddr_t -> list ptable_pointer.

Axiom is_aligned : uintpaddr_t -> nat (* PAGE_SIZE *) -> bool.

(* equality of the paddr_t type is decidable *)
Axiom paddr_t_eq_dec : forall (a1 a2 : paddr_t), {a1 = a2} + {a1 <> a2}.
Axiom pa_from_va_id : forall (a : paddr_t), pa_from_va (va_from_pa a) = a.
Axiom va_init_id : forall (a : vaddr_t), va_init (va_addr a) = a.
