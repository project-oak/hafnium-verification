Require Import ListSet.
Require Import Arith.
Require Import Coq.Lists.List.
Require Import Mailbox.global_state.
Require Import Mailbox.utils.
Require Import Mailbox.switch_to_primary.

(*-------------------------------------------------------------------------*)
(* Send                                                                    *)
(*-------------------------------------------------------------------------*)
Record sendargs : Set := {
    sender_vm_id: vmid;
    receiver_vm_id: vmid;
    size: nat;
    attributes: Empty_set; (* TODO *)
    _current: Empty_set;
    next: Empty_set;
}.
(* TODO learn how to make uninterpreted set declarations *)

(* Returns true when HVC would error instead of executing. *)
Inductive sendRet: Set :=
    | sendRetError
    | sendRetSucc
    | sendRetBusy.

(* TODO *)
Definition sendErrs (s: hfstate) (to: vmid) (args: sendargs): bool := 
    let from := current s in
    if
        andb (eqid (sender_vm_id args) (id from))
        (eqid (receiver_vm_id args) (id from))
         (* TODO find way to represent NULL vmid
            andb ((SPCI_MSG_PAYLOAD_MAX s) <? (size args))
            (
              andb (sendb vmboxes from =? 0)
              (eqid (to) 0)
            )
          )
        ) *)
    then true
    else false.

(* sendArchitected is how page permissions are changed. 
*  It is a special case of the send HVC (depending on args) *)
Definition doSendArchitected (args : sendargs): bool := false. (* TODO *)
Definition sendArchitected (s: hfstate) (to from : vmid) (args: sendargs):
    (hfstate * sendRet) :=
    (s, sendRetError). (* TODO *)

Definition doNotify (args: sendargs) : bool := false. (* TODO *)

Definition send (s: hfstate) (to: vmid) (args: sendargs):
    (hfstate * sendRet) :=
    let from := current s in
    let oldto := (vmboxes s) to in
    let oldfrom := (vmboxes s) from in
    if sendErrs s to args then (s, sendRetError)
    else match state oldto with 
        | Empt => 
            if doSendArchitected args 
                then sendArchitected s to from args
                else let toprime := Mailbox Recv (sendb oldto)
                    (sendb oldfrom ) (waiters oldto) in
                    let sprime := updvmbox s to toprime in
                    if eqid Primary to then 
						(switchToPrimary sprime VCPU_STATE_READY,
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
