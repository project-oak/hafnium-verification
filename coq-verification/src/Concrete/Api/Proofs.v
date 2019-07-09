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

Require Import Coq.Arith.PeanoNat.
Require Import Hafnium.AbstractModel.
Require Import Hafnium.Concrete.State.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.Mpool.
Require Import Hafnium.Concrete.Api.Implementation.

Lemma api_clear_memory_valid
      {cp : concrete_params} (conc : concrete_state) begin end_ ppool :
  is_valid conc ->
  let conc' := snd (fst (api_clear_memory conc begin end_ ppool)) in
  is_valid conc'.
Proof.
  tauto. (* N.B. this proof is trivial because is_valid isn't yet filled in *)
Qed.

Lemma api_clear_memory_represents
      {ap : abstract_state_parameters} {cp : concrete_params}
      (abst : abstract_state) (conc : concrete_state)
      begin end_ ppool :
  represents abst conc ->
  let conc' := snd (fst (api_clear_memory conc begin end_ ppool)) in
  exists abst', represents abst' conc'.
Proof.
Admitted. (* TODO *)

Lemma api_share_memory_valid
      {cp : concrete_params} (conc : concrete_state)
      vid addr size share current :
  is_valid conc ->
  let conc' := snd (api_share_memory conc vid addr size share current) in
  is_valid conc'.
Proof.
  tauto. (* N.B. this proof is trivial because is_valid isn't yet filled in *)
Qed.

Lemma api_share_memory_represents
      {ap : abstract_state_parameters} {cp : concrete_params}
      (abst : abstract_state) (conc : concrete_state)
      vid addr size share current :
  represents abst conc ->
  let conc' := snd (api_share_memory conc vid addr size share current) in
  exists abst', represents abst' conc'.
Proof.
Admitted. (* TODO *)
