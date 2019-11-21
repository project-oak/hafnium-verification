Require Import Mailbox.global_state.
Require Import Mailbox.utils.
Require Import Mailbox.switch_to_primary.
Require Import ZArith.

(*-------------------------------------------------------------------------*)
(* fetch_waiter                                                            *)
(*-------------------------------------------------------------------------*)

(* if VM's mailbox initialized, empty, and there is a waiter,
 *   remove the first waiter and return it
 * otherwise return an invalid VM ID *)
 
(* hsk waiter list can be abstracted nothing else *)
(* hsk we can't check if mailbox is initialized yet *)

Definition fetch_waiter (s: hfstate) (vm_id : vmid) : (vmid * hfstate) :=
     (* get the mailbox *)
     let mailbox := (vmboxes s) vm_id in
          (* check the mailbox's state *)
          match state mailbox with
               (* if empty *) 
               | Empt =>
                    (* check waiters *)
                    match waiters mailbox with
                         (* if there is no waiter, cannot fetch a waiter *)
                         | nil => (Invalid, s)
                         (* if there is a waiter, return the first waiter and updated state *)
                         | cons first_waiter waiters' =>
                              (first_waiter, (updvmbox s vm_id (remwaiter mailbox)))
                    end
               (* if not empty, cannot fetch a waiter *)
               | _ => (Invalid, s)
          end. 

(*-------------------------------------------------------------------------*)
(* waiter_get                                                              *)
(*-------------------------------------------------------------------------*)

(* hsk ready list can be abstracted but nothing else *)

(* if current VM is not primary VM, return -1
if the specified VM ID is invalid, return -1
remove an entry from the specified VM's waiter list
if the entry is empty, return -1
if the entry is not already in the waiting VM's ready list, add it
return waiting VM's ID *) 

Definition waiter_get (s: hfstate) (vm_id : vmid) (current_vcpu : vmid) : (vmid * hfstate) :=
     match vm_id with
          | Primary =>
               (* Assume that vm_id is valid *)
               (* TODO : should undate the ready list of the waiting VM *)
               let (waiter, s') := fetch_waiter s vm_id in
                    match waiter with
                         | Invalid => (Invalid, s)
                         | _ => (waiter, s')
                    end
          | _ => (Invalid, s)
     end.
