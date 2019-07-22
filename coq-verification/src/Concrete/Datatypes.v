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

(* hf_share enum *)
Inductive hf_share :=
| HF_MEMORY_GIVE
| HF_MEMORY_LEND
| HF_MEMORY_SHARE
| INVALID
.
