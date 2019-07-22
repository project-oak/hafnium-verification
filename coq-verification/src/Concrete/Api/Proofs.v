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
Require Import Hafnium.Util.Tactics.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.Mpool.
Require Import Hafnium.Concrete.Api.Implementation.
Require Import Hafnium.Concrete.MM.Proofs.

Lemma api_clear_memory_valid
      {cp : concrete_params} (conc : concrete_state) begin end_ ppool :
  is_valid conc ->
  let conc' := snd (fst (api_clear_memory conc begin end_ ppool)) in
  is_valid conc'.
Proof.
  tauto. (* N.B. this proof is trivial because is_valid isn't yet filled in *)
Qed.

Lemma api_clear_memory_represents
      {ap : @abstract_state_parameters paddr_t nat} {cp : concrete_params}
      (abst : abstract_state) (conc : concrete_state)
      begin end_ ppool :
  represents_valid abst conc ->
  let conc' := snd (fst (api_clear_memory conc begin end_ ppool)) in
  exists abst', represents_valid abst' conc'.
Proof.
  cbv [api_clear_memory].
  repeat match goal with
         | _ => progress basics
         | _ => progress cbn [fst snd]
         | |- context [let '(_,_) := ?x in _] =>
           rewrite (surjective_pairing x)
         | _ => progress break_match
         | _ => apply mm_defrag_represents
         | _ => apply mm_unmap_represents
         | _ => apply mm_identity_map_represents
         | _ => solver
         end.
Qed.

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
      {ap : @abstract_state_parameters paddr_t nat} {cp : concrete_params}
      (abst : abstract_state) (conc : concrete_state)
      vid addr size share current :
  represents_valid abst conc ->
  let conc' := snd (api_share_memory conc vid addr size share current) in
  exists abst', represents_valid abst' conc'.
Proof.
Admitted. (* TODO *)
