Require Import ListSet.
Require Import Coq.Lists.List.
Require Import Mailbox.global_state.
Require Import Mailbox.utils.
Require Import Mailbox.switch_to_primary.

(*-------------------------------------------------------------------------*)
(* Send                                                                    *)
(*-------------------------------------------------------------------------*)
Definition sendargs : Set := nat.
(* TODO learn how to make uninterpreted set declarations *)

(* Returns true when HVC would error instead of executing. *)
Inductive sendRet: Set :=
    | sendRetError
    | sendRetSucc
    | sendRetBusy.

(* TODO *)
Definition sendErrs (s: hfstate)(args: sendargs): bool := false.

(* sendArchitected is how page permissions are changed. 
*  It is a special case of the send HVC (depending on args) *)
Definition doSendArchitected (args : sendargs): bool := false. (* TODO *)
Definition sendArchitected (s: hfstate) (to from : vmid) (args: sendargs):
    (hfstate * sendRet) :=
    (s, sendRetError). (* TODO *)

Definition doNotify (args: sendargs) : bool := false. (* TODO *)

(* TODO aferr: recheck some_spci_value. I have no idea if this makes sense.
* just added while working on switchToPrimary *)

Definition send (s: hfstate) (to: vmid ) 
    (args: sendargs )(some_spci_value: spci_value):
  (hfstate * sendRet) :=
    let from := current s in
    let oldto := (vmboxes s) to in
    let oldfrom := (vmboxes s) from in
    if sendErrs s args then (s, sendRetError)
    else match state oldto with 
        | Empt => 
            if doSendArchitected args 
                then sendArchitected s to from args
                else let toprime := Mailbox Recv (sendb oldto)
                    (sendb oldfrom ) (waiters oldto) (readylist oldto) in
                    let sprime := updvmbox s to toprime in
                    if eqid Primary to then 
                    (* TODO Fix the primary_ret *)
						(switchToPrimary sprime VCPU_STATE_READY some_spci_value,
                        	sendRetSucc)
                    else (sprime, sendRetSucc)
        | _ => 
            if doNotify args then 
                let toprime := updwaiter oldto from in
                (updvmbox s to toprime, sendRetBusy)
            else (s, sendRetBusy)
            (* receiver mailbox not empty, so we need to either
            * notify or block *)
    end.
