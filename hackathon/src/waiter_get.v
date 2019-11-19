Require Import Mailbox.global_state.
Require Import Mailbox.utils.
Require Import Mailbox.switch_to_primary.

(*-------------------------------------------------------------------------*)
(* fetch_waiter                                                            *)
(*-------------------------------------------------------------------------*)

(* hsk waiter list can be abstracted
 * nothing else *)

if VM's mailbox is not empty or not initialized or no waiter
     return NULL

entry <- remove the first waiter in the waiter list
return entry

(*-------------------------------------------------------------------------*)
(* waiter_get                                                              *)
(*-------------------------------------------------------------------------*)

(* hsk ready list can be abstracted
 * nothing else *)

waiter_get

if current VM is not primary VM, return -1
if the specified VM ID is invalid, return -1
remove an entry from the specified VM's waiter list
if the entry is empty, return -1
if the entry is not already in the waiting VM's ready list, add it
return waiting VM's ID

