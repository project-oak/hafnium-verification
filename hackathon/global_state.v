Require Import ListSet.
Require Import Coq.Lists.List.

(*-------------------------------------------------------------------------*)
(* Hafnium State                                                           *)
(*-------------------------------------------------------------------------*)

Inductive maybe (t: Set) : Set :=
  | Some: t -> maybe t
  | None: maybe t.

(* TODO should we make this an uninterpreted finite set ? *)
Definition msg : Set := nat.

Inductive vmid : Set :=
  | Primary: vmid           
  | Secondary : nat -> vmid.

Definition wlist := list vmid.

Inductive mboxState : Set :=
    | Read : mboxState
    | Recv : mboxState
    | Empt : mboxState.

Record mailbox : Set  := Mailbox {
    state: mboxState;
    sendb: maybe msg;
    recvb: maybe msg;
    waiters: wlist
}.

Record hfstate: Set := HFState {
	(* TODO eventually need more complete model of VM state. Reachable memory,
    * etc.*)
    (*TODO model of VCPUs ? *)
    vmboxes: vmid -> mailbox;
    current: vmid;
}.
