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
Require Import Hafnium.Util.List.
Require Import Hafnium.Util.Tactics.
Import ListNotations.

(*** High-level model : describes the abstract state of the Hafnium system ***)

Section Abstract.
  (* Assume a type of addresses, and that their equality is decidable. The
     addresses are in Hafnium's address space (physical addresses, if Hafnium
     runs on bare metal). All addresses in this type are assumed to be aligned to
     the page size; they're really more like "page addresses". *)
  Context {addr : Type}
          {addr_eq_dec : forall a1 a2 : addr, {a1 = a2} + {a1 <> a2}}.

  (* assume a type of unique identifier for VMs, and that equality between VM ids
     is decidable *)
  Context {vm_id : Type}
          {vm_id_eq_dec : forall id1 id2 : vm_id, {id1 = id2} + {id1 <> id2}}.

  (* set the unique identifier for Hafnium to the [unit] type; since there is
     only one member of this type (called [tt]), there is only one id for
     Hafnium itself.*)
  Definition hafnium_id : Type := unit.
  Definition hid : hafnium_id := tt.

  (* an entity is either a VM or Hafnium ("+" means "or") *)
  Definition entity_id : Type := vm_id + hafnium_id.

  (* boilerplate: convert vm_ids and hafnium_id to entity_id if needed *)
  Local Definition inl_entity : vm_id -> entity_id := @inl vm_id hafnium_id.
  Local Definition inr_entity : hafnium_id -> entity_id := @inr vm_id hafnium_id.
  Local Coercion inl_entity : vm_id >-> entity_id.
  Local Coercion inr_entity : hafnium_id >-> entity_id.
  Hint Unfold inl_entity inr_entity.
  Set Printing Coercions.

  (* boilerplate: decidability for the entity_id type *)
  Definition entity_id_eq_dec (i1 i2 : entity_id) : {i1 = i2} + {i1 <> i2}.
  Proof.
    destruct i1, i2;
      repeat match goal with
             | _ => progress subst
             | _ => right; congruence
             | _ => left; congruence
             | x : hafnium_id |- _ => destruct x
             | |- {inl ?v1 = inl ?v2} + { _ } => destruct (vm_id_eq_dec v1 v2)
             end.
  Defined.

  (* unchanging starting parameters of the global state *)
  Class abstract_state_parameters :=
    {
      vms : list vm_id;
      hafnium_reserved : addr -> bool;
    }.
  
  (* Global abstract state : all addresses are owned by one particular entity (a
     VM or Hafnium), and accessible by a certain set of entities. This
     is a global way of capturing the V/O/X bits in Hafnium's page tables. For
     reference, the description of these states given in the Hafnium source
     is copied here:
     
     ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     The states are made up of three parts:
     
      1. V = valid/invalid    : Whether the memory is part of the VM's address
                                space. A fault will be generated if accessed when
                                invalid.
      2. O = owned/unowned    : Whether the memory is owned by the VM.
      3. X = exclusive/shared : Whether access is exclusive to the VM or shared
                                with at most one other.
     
     These parts compose to form the following state:
     
      -  V  O  X : Owner of memory with exclusive access.
      -  V  O !X : Owner of memory with access shared with at most one other VM.
      -  V !O  X : Borrower of memory with exclusive access.
      -  V !O !X : Borrower of memory where access is shared with the owner.
      - !V  O  X : Owner of memory lent to a VM that has exclusive access.
     
      - !V  O !X : Unused. Owner of shared memory always has access.
     
      - !V !O  X : Invalid memory. Memory is unrelated to the VM.
      - !V !O !X : Invalid memory. Memory is unrelated to the VM.
     ~~~~~~~~~~~~~~~~~~~~~~

     These codes, however, are all from the perspective of a single entity, while
     this model needs to reason at a more global conceptual level about who can
     access a piece of memory, and who owns it. Therefore, we translate these
     attribute bits into global concepts according to the table below:

     If entity "me" sees... | then the global state of that page is...
                            | [accessible_by]         | [owned_by]
     ======================================================================
      V  O  X               | me                      | me
      V  O !X               | me, <someone else>      | me
      V !O  X               | me                      | <someone else>
      V !O !X               | me, <someone else>      | <same someone else>
     !V  O  X               | <someone else>          | me
     !V  O !X               | -----------------unused---------------------- 
     !V !O  X               | <not me; 1 or 2 others> | <someone else>
     !V !O !X               | <not me; 1 or 2 others> | <someone else>

   *)
  Class abstract_state :=
    {
      (* accessible_by is a function from address to list of entity IDs *)
      accessible_by : addr -> list entity_id;
      (* owned_by is a function from address to list of entity IDs *)
      owned_by : addr -> entity_id;
    }.

  (*** The following definitions describe some basic operations on the abstract
       state. Each takes a current state as input and returns a new state. ***)

  (* if VM with ID [from_id] has access to memory at address [a], revoke it. *)
  Definition revoke_access
             (s : abstract_state) (from_id : vm_id) (a : addr)
    : abstract_state :=
    {|
      (* new accessibility state *)
      accessible_by := (fun a' =>
                          (* to look up an address a', first check if a' == a *)
                          if addr_eq_dec a a'
                          then
                            (* a = a'; look up who could access a' in the
                               previous state, remove all occurrences of
                               [from_id] from the list, and return it *)
                            remove entity_id_eq_dec from_id (accessible_by a')
                          else
                            (* a != a'; return the list from previous state *)
                            accessible_by a');
      (* owned_by doesn't change *)
      owned_by := owned_by
    |}.

  (* add [to_id] to the list of entities that can access memory at address [a] *)
  Definition allow_access
             (s : abstract_state) (to_id : entity_id) (a : addr)
    : abstract_state :=
    {|
      (* new accessibility state *)
      accessible_by := (fun a' =>
                          (* to look up an address a', first check if a' == a *)
                          if addr_eq_dec a a'
                          then
                            (* a = a'; look up who could access a' in the
                               previous state, add [to_id] to the list, and
                               return it *)
                            to_id :: accessible_by a'
                          else
                            (* a != a'; return the list from previous state *)
                            accessible_by a');
      (* owned_by doesn't change *)
      owned_by := owned_by
    |}.

  (* set the entity with ID [to_id] as the owner of memory at address [a]  *)
  Definition set_owner
             (s : abstract_state) (to_id : entity_id) (a : addr)
    : abstract_state :=
    {|
      (* accessible_by doesn't change *)
      accessible_by := accessible_by;
      (* new ownership state *)
      owned_by := (fun a' =>
                     (* to look up an address a', first check if a' == a *)
                     if addr_eq_dec a a'
                     then
                       (* a = a'; to_id is the owner *)
                       to_id
                     else
                       (* a != a'; get the owner from the old state*)
                       owned_by a')
    |}.

  (* tell [autounfold] to unfold these definitions *)
  Hint Unfold revoke_access allow_access set_owner.

  (*** Define giving/sharing/lending memory in terms of the basic operations ***)

  Definition give (s : abstract_state) (from_id to_id : vm_id) (a : addr)
    : abstract_state := set_owner (allow_access (revoke_access s from_id a) to_id a) to_id a.

  Definition share (s : abstract_state) (from_id to_id : vm_id) (a : addr)
    : abstract_state := allow_access s to_id a.

  Definition lend (s : abstract_state) (from_id to_id : vm_id) (a : addr)
    : abstract_state := allow_access (revoke_access s from_id a) to_id a.

  (* tell [autounfold] to unfold these definitions *)
  Hint Unfold give share lend.

  (*** shortcut statements about the global state to make [is_valid] more
       readable ***)

  Local Definition has_access {s : abstract_state} (id : entity_id) (a : addr) :=
    In id (accessible_by a).
  Local Definition has_exclusive_access
        {s : abstract_state} (id : entity_id) (a : addr) :=
    accessible_by a = [id].
  Local Definition owns {s : abstract_state} (id : entity_id) (a : addr) :=
    owned_by a = id.

  (* tell [autounfold] to unfold these definitions *)
  Hint Unfold has_access has_exclusive_access owns.

  (* TODO: for now, Hafnium itself can't participate in lending/sharing/giving,
     but eventually we will need to deal with send/recv buffers. *)

  (* inductive definition of valid operations on an abstract state *)
  Inductive is_valid {params : abstract_state_parameters}
    : abstract_state -> Prop :=
  (* initial state: no memory is shared *)
  | AbstractInit :
      forall (owned_by_init : addr -> entity_id),

        (* precondition on the initial assignment *)
        (forall a,
            if hafnium_reserved a
            then
              (* if the address is marked as reserved for Hafnium, then it indeed
                 belongs to Hafnium (whose ID is [hid]) *)
              owned_by_init a = inr hid
            else
              (* otherwise, it belongs to a VM whose ID is in the [vms] list *)
              exists vid, owned_by_init a = inl vid /\ In vid vms) ->

        is_valid
          {|
            (* only the owner has access *)
            accessible_by := fun a => [owned_by_init a];
            owned_by := owned_by_init;
          |}

  (* a VM can give memory it owns to another VM *)
  | AbstractGive :
      forall (state : abstract_state) (from_id to_id : vm_id) (a : addr),
        (* if previous state is valid *)
        is_valid state ->
        (* ...and requesting VM has exclusive access *)
        has_exclusive_access from_id a ->
        (* ...and requesting VM owns the memory *)
        owns from_id a ->
        (* ...and the destination VM ID exists *)
        In to_id vms ->
        (* ...then state is valid after [give] *)
        is_valid (state.(give) from_id to_id a)

  (* a VM can give back memory previously shared/lent to it *)
  | AbstractReturn :
      forall (state : abstract_state) (from_id to_id : vm_id) (a : addr),
        (* if previous state is valid *)
        is_valid state ->
        (* ...and requesting VM has access *)
        has_access from_id a ->
        (* ...and the *destination* VM owns the memory *)
        owns to_id a ->
        (* ...then state is valid after [give] *)
        is_valid (state.(give) from_id to_id a)

  (* a VM can give one other VM access to memory it owns *)
  | AbstractShare :
      forall (state : abstract_state) (from_id to_id : vm_id) (a : addr),
        (* if previous state is valid *)
        is_valid state ->
        (* ...and requesting VM has exclusive access *)
        has_exclusive_access from_id a ->
        (* ...and requesting VM owns the memory *)
        owns from_id a ->
        (* ...and the destination VM ID exists *)
        In to_id vms ->
        (* ...then state is valid after [share] *)
        is_valid (state.(share) from_id to_id a)

  (* a VM can give exclusive access to one other VM *)
  | AbstractLend :
      forall (state : abstract_state) (from_id to_id : vm_id) (a : addr),
        (* if previous state is valid *)
        is_valid state ->
        (* ...and requesting VM has exclusive access *)
        has_exclusive_access from_id a ->
        (* ...and requesting VM owns the memory *)
        owns from_id a ->
        (* ...and the destination VM ID exists *)
        In to_id vms ->
        (* ...then state is valid after [lend] *)
        is_valid (state.(lend) from_id to_id a)
  .

  Definition obeys_invariants
             {params : abstract_state_parameters}
             (state : abstract_state) : Prop :=
    (* all the VMs mentioned in accessibility state exist in the system *)
    (forall (vid : vm_id) (a : addr), has_access vid a -> In vid vms)
    (* ...and all the VMs mentioned in ownership state exist in the system *)
    /\ (forall (vid : vm_id) (a : addr), owns vid a -> In vid vms)
    (* ...and at least one entity always has access to memory *)
    /\ (forall a, exists (e : entity_id), has_access e a)
    (* ...and memory is accessible by at most 2 VMs *)
    /\ (forall a, length (accessible_by a) <= 2)
    (* ...and no one has access to Hafnium's memory but Hafnium (id = [hid]) *)
    /\ (forall a, hafnium_reserved a = true ->
                  forall (id : entity_id), has_access id a -> id = inr hid).

  (* TODO: VMs only have access if another VM gave/shared/lent it to them in
     the past -- requires reasoning about traces *)

  (* tell [solver] to try solving goals with properties of [In] *)
  Hint Resolve in_cons in_eq.

  (* if the state is valid, then the state obeys the invariants *)
  Lemma valid_obeys_invariants {params : abstract_state_parameters} :
    forall s, is_valid s -> obeys_invariants s.
  Proof.
    cbv [obeys_invariants]; induction 1;
      repeat match goal with
             | _ => progress basics
             | _ => progress break_match
             | _ => progress autounfold in *
             | _ => progress invert_list_properties
             | _ => progress autorewrite with push_length
             | _ => progress cbn [accessible_by owned_by] in *
             | H : (forall a, if hafnium_reserved a then _ else _),
                   a : addr |- _ => specialize (H a)
             | H : _ |- _ => apply In_remove in H
             | H : accessible_by _ = cons _ _ |- _ => rewrite H
             | H : _ |- context [length (remove ?dec ?x ?ls)] =>
               pose proof (remove_length_lt dec x ls H); solver
             | |- context [length (remove ?dec ?x ?ls)] =>
               pose proof (remove_length_le dec x ls);
                 autorewrite with push_length in *; solver
             | H : (forall a, hafnium_reserved a  = true -> _),
                   H' : hafnium_reserved _ = true |- _ =>
               eapply H in H'; [| try match goal with
                                        H : accessible_by _ = _ |- _ =>
                                        rewrite H end; solver]
             | H : forall a, length (accessible_by a) <= _
                              |- context [accessible_by ?a] => specialize (H a)
             | _ => eexists; cbn; repeat break_match; solver
             | _ => solver
             end.
  Qed.

End Abstract.
