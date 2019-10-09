Require Import ListSet.
<<<<<<< HEAD
Require Import Coq.Lists.List.

(*aferr: idk if maybe already exists in coq*)
Inductive maybe (t: Set) : Set :=
  | Some: t -> maybe t
  | None: maybe t.
=======
>>>>>>> a4cd7d8a093db7909e9cfbec4f72d59df902952e

(*-------------------------------------------------------------------------*)
(* Hafnium State                                                           *)
(*-------------------------------------------------------------------------*)
<<<<<<< HEAD

(* TODO make this an uninterpreted finite set *)
Definition msg : Set := nat.

=======
(*aferr: idk if maybe already exists*)
Inductive maybe (t: Set) : Set :=
  | Some: t -> maybe t
  | None: maybe t.

Definition msg : Set := nat.
>>>>>>> a4cd7d8a093db7909e9cfbec4f72d59df902952e
Inductive vmid : Set :=
  | Primary: vmid
  | Secondary : nat -> vmid.

Definition wlist := list vmid.
<<<<<<< HEAD

(*aferr: I do not yet understand why there are separate Read and empty states
* or why there needs to be a separate call to clear the mailbox. Why can't the rreceive call just move from the received state to the empty state *)
Inductive mboxState : Set := 
    | Read : mboxState
    | Recv : mboxState
    | Empt : mboxState.

Record mailbox : Set := Mailbox {
    state: mboxState;
    sendb: maybe msg; 
    recvb: maybe msg; 
    waiters: wlist
}.

Eval simpl in (Mailbox Read (Some nat 3) (Some nat 4) nil).

(*TODO model of VCPUs *)
Record hfstate: Set := HFState {
	(* TODO eventually need more complete model of VM state *)
    vmboxes: vmid -> mailbox;
    current: vmid;
=======
Record mailbox : Set := Mailbox {
    sendb: maybe msg; recvb: maybe msg; waiters: wlist
}.

Eval simpl in (Mailbox (Some nat 3) (Some nat 4) nil).

Record hfstate: Set := HFState {
    vmboxes: vmid -> mailbox;
    next: vmid
>>>>>>> a4cd7d8a093db7909e9cfbec4f72d59df902952e
}.

(*-------------------------------------------------------------------------*)
(* Utilities                                                               *)
(*-------------------------------------------------------------------------*)
Definition eqid (x y: vmid): bool :=
    match (x, y) with
        | (Primary, Primary) => true
        | (Secondary xx, Secondary yy) => Nat.eqb xx yy
        | (_, _) => false
    end.

<<<<<<< HEAD
(* state mutators *)
Definition updvmbox (s: hfstate)(id: vmid)(mb: mailbox): hfstate :=
    {| 
        vmboxes := fun x: vmid => if eqid id x then mb else (vmboxes s) x;
        current := current s;
    |}.

(* mailbox mutators *)
(* TODO only add to list if it is not already present in the list *)
Definition updwaiter (mb: mailbox)(id: vmid): mailbox :=
    {|
        state := state mb;
        sendb := sendb mb; 
        recvb := recvb mb; 
        waiters := id :: (waiters mb);
    |}.

(* mailbox mutators *)
Definition updstate (mb: mailbox)(s: mboxState): mailbox :=
    {|
        state := s;
        sendb := sendb mb; 
        recvb := recvb mb; 
        waiters := waiters mb;
    |}.
        
(*-------------------------------------------------------------------------*)
(* HVCs                                                                    *)
(*-------------------------------------------------------------------------*)

(*-------------------------------------------------------------------------*)
(* Switch to Primary *)
(*-------------------------------------------------------------------------*)
(* This is called by send and recv and causes an immediate context switch
* to the primary VM *)
(* It is not filled in, but the important thing is that the primary VM does
know that it is executing *)

(* This is almost verbatim copy-pasted from the C *)
Inductive vcpuState: Set:=
	(* The vcpu is switched off. *)
	| VCPU_STATE_OFF

	(* The vcpu is ready to be run. *)
	| VCPU_STATE_READY

	(* The vcpu is currently running. *)
	| VCPU_STATE_RUNNING

	(* The vcpu is waiting for a message. *)
	| VCPU_STATE_BLOCKED_MAILBOX

	(* The vcpu is waiting for an interrupt. *)
	| VCPU_STATE_BLOCKED_INTERRUPT

	(* The vcpu has aborted. *)
	| VCPU_STATE_ABORTED.

(* TODO *)
Definition switchToPrimary(s: hfstate)(code: vcpuState): hfstate := s.

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

Definition send (s: hfstate) (to: vmid) (args: sendargs):
  (hfstate * sendRet) :=
    let from := current s in
    let oldto := (vmboxes s) to in
    let oldfrom := (vmboxes s) from in
    if sendErrs s args then (s, sendRetError)
    else match state oldto with
        | Empt => 
            (* receiver mailbox empty, so we can do the send *)
            if doSendArchitected args
                then sendArchitected s to from args
                else let toprime := Mailbox Recv (sendb oldto)
                    (sendb oldfrom) (waiters oldto) in
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
=======

Definition updvmbox (s: hfstate)(id: vmid)(mb: mailbox): hfstate :=
    {| 
        vmboxes := fun x: vmid => if eqid id x then mb else (vmboxes s) x;
        next := next s
    |}.

Definition updnext (s: hfstate)(id: vmid): hfstate :=
    {| 
        vmboxes := vmboxes s;
        next := id
    |}.

(*-------------------------------------------------------------------------*)
(* HVCs                                                                    *)
(*-------------------------------------------------------------------------*)
Definition sendargs : Set := nat.

(* TODO learn how to make "uninterpreted function declarations" *)

(* Returns true when HVC would error instead of executing. *)
Definition sendErrs: hfstate -> sendargs -> bool :=
    fun x => fun y => false. (* TODO *)

(* sendArchitected is how page permissions are changed. 
*  It is a special case of the send HVC (depending on args) *)
Definition doSendArchitected : sendargs -> bool := fun x => false. (* TODO *)
Definition sendArchitected (s: hfstate) (to from : vmid) (args: sendargs):
    (hfstate * bool) :=
    (s, false). (* TODO *)

Definition doNotify (args: sendargs) : bool := false. (* TODO *)

Definition send (s: hfstate) (to from: vmid) (args: sendargs):
  (hfstate * bool) :=
    let oldto := (vmboxes s) to in
    let oldfrom := (vmboxes s) from in
    if sendErrs s args then (s, true)
    else match recvb oldto with
        | None _ => 
            (* receiver mailbox empty, so we can do the send *)
            if doSendArchitected args
                then sendArchitected s to from args
                else let toprime := Mailbox (sendb oldto)
                    (sendb oldfrom) (waiters oldto ) in
                   (* need to update state! *)
                    let sprime := updvmbox s to toprime in
                    if eqid Primary to then (updnext sprime Primary, false)
                    else (sprime, false)
        | Some _ _ => (s, false) (* TODO *)
                (* need to better understand waitlist
                behavior. for now just leaving this stub.*)
>>>>>>> a4cd7d8a093db7909e9cfbec4f72d59df902952e
            (* receiver mailbox not empty, so we need to either
            * notify or block *)
    end.


<<<<<<< HEAD
(*-------------------------------------------------------------------------*)
(* Recv                                                                    *)
(*-------------------------------------------------------------------------*)
(*aferr: Note that AFAICT this call does not actually do anything with the data
* in the reveive buffer. It just changes the mailbox state on a successful call. Presumably the expectation is that between the recv call and the clear call hthe caller will manually copy the data out of the receive buffer. *)

Inductive recvRet: Set :=
    | recvRetSucc
    | recvRetRetry
    | recvRetInt.

Definition recv (s: hfstate) (block: bool):  (hfstate * recvRet) :=
    let cur := current s in
    let curbox := (vmboxes s) cur in
    if eqid cur Primary then (s, recvRetInt)
    else match state curbox with
        | Recv => (updvmbox s cur (updstate curbox Read), recvRetSucc)
        | _ => match block with
            | false => (s, recvRetRetry)
            | true => ((switchToPrimary s VCPU_STATE_BLOCKED_MAILBOX), recvRetSucc)
        end
    end.
=======
>>>>>>> a4cd7d8a093db7909e9cfbec4f72d59df902952e
