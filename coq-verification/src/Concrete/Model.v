Require Import Coq.Lists.List.
Require Import Hafnium.AbstractModel.
Require Import Hafnium.Concrete.State.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.Mpool.
Require Import Hafnium.Concrete.Api.Implementation.

(*** This file gives the definition of execution in the concrete model and
     includes the highest-level correctness proof, stating that the execution
     rules of the concrete model obey the system invariants. ***)

Inductive api_call : Type :=
| clear_memory : paddr_t -> paddr_t -> mpool -> api_call
| share_memory : nat -> ipaddr_t -> size_t -> hf_share -> vm -> api_call
.

Fixpoint execute_trace
         {cp : concrete_params}
         (start_state : concrete_state)
         (trace : list api_call) : concrete_state :=
  fold_right (fun next_call state =>
                match next_call with
                | clear_memory begin end_ ppool =>
                  let '(_, state', _) :=
                      api_clear_memory state begin end_ ppool in
                  state'
                | share_memory vid addr size share current =>
                  let '(_, state') :=
                      api_share_memory state vid addr size share current in
                  state'
                end)
             start_state trace.

(* A concrete state obeys the invariants if it's represented by an abstract
   state that obeys them. *)
Definition obeys_invariants
           {ap : abstract_state_parameters} {cp : concrete_params}
           (conc : concrete_state) : Prop :=
  exists abst : abstract_state,
    represents abst conc /\ AbstractModel.obeys_invariants abst.

(*** Highest-level correctness theorem: any execution of api calls will preserve
     the invariants; that is, if you obey the invariants at the start, no
     sequence of api calls can make you stop obeying them. ***)
Theorem execution_preserves_invariants :
  forall {ap : abstract_state_parameters} {cp : concrete_params}
         (start_state : concrete_state) (trace : list api_call),
    obeys_invariants start_state ->
    obeys_invariants (execute_trace start_state trace).
Proof.
Admitted. (* TODO *)
