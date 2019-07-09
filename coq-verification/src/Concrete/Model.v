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

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Hafnium.AbstractModel.
Require Import Hafnium.Concrete.State.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Util.Tactics.
Require Import Hafnium.Concrete.Api.Implementation.
Require Import Hafnium.Concrete.Api.Proofs.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.Mpool.

(*** This file gives the definition of execution in the concrete model and
     includes the highest-level correctness proof, stating that the execution
     rules of the concrete model obey the system invariants. ***)

Inductive api_call : Type :=
| clear_memory : paddr_t -> paddr_t -> mpool -> api_call
| share_memory : nat -> ipaddr_t -> size_t -> hf_share -> vm -> api_call
.

Definition execute_trace
           {cp : concrete_params}
           (start_state : concrete_state)
           (trace : list api_call) : concrete_state :=
  fold_right (fun next_call state =>
                match next_call with
                | clear_memory begin end_ ppool =>
                  let ret := api_clear_memory state begin end_ ppool in
                  snd (fst ret)
                | share_memory vid addr size share current =>
                  let ret := api_share_memory state vid addr size share current in
                  snd ret
                end)
             start_state trace.

(* A concrete state obeys the invariants if it's represented by an abstract
   state that obeys them. *)
Definition obeys_invariants
           {ap : abstract_state_parameters} {cp : concrete_params}
           (conc : concrete_state) : Prop :=
  exists abst : abstract_state,
    represents abst conc /\ AbstractModel.obeys_invariants abst.

(* because [represents] includes [AbstractModel.is_valid], and we've proved all
   valid abstract states obey the invariants, it's sufficient to just prove
   [represents] *)
Lemma represents_obeys_invariants
      {ap : abstract_state_parameters} {cp : concrete_params}
      (conc : concrete_state) :
  (exists abst, represents abst conc) ->
  obeys_invariants conc.
Proof.
  cbv [represents obeys_invariants]; basics.
  eexists; basics; try solver; [ ].
  apply (valid_obeys_invariants
           (addr_eq_dec:=paddr_t_eq_dec) (vm_id_eq_dec:=Nat.eq_dec)).
  eauto.
Qed.

Lemma execution_represents
      {ap : abstract_state_parameters} {cp : concrete_params}
      (start_state : concrete_state) (trace : list api_call) :
  (exists abst, represents abst start_state) ->
  exists abst, represents abst (execute_trace start_state trace).
Proof.
  cbv [execute_trace]; intros; induction trace; [ basics; solver | ].
  destruct IHtrace as [abst IHtrace]. basics.
  cbn [fold_right]. break_match.
  { (* case : api_clear_memory *)
    apply api_clear_memory_represents with (abst0:=abst).
    eapply IHtrace. }
  { (* case : api_share_memory *)
    apply api_share_memory_represents with (abst0:=abst).
    eapply IHtrace. }
Qed.

(*** Highest-level correctness theorem: any execution of api calls will preserve
     the invariants; that is, if you obey the invariants at the start, no
     sequence of api calls can make you stop obeying them. ***)
Theorem execution_preserves_invariants
        {ap : abstract_state_parameters} {cp : concrete_params} :
  forall (trace : list api_call) (start_state : concrete_state),
    obeys_invariants start_state ->
    obeys_invariants (execute_trace start_state trace).
Proof.
  intros; apply represents_obeys_invariants, execution_represents.
  cbv [obeys_invariants] in *. basics; solver.
Qed.

(* Uncomment the below to see all assumptions that the top-level correctness
   theorem depends on. *)
(* Print Assumptions execution_preserves_invariants. *)
