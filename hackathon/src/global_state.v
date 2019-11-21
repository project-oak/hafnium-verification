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
  | Invalid: vmid
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
    waiters: wlist;
    readylist: wlist;
}.

Record hfstate: Set := HFState {
	(* TODO eventually need more complete model of VM state. Reachable memory,
    * etc.*)
    (*TODO model of VCPUs ? *)
    vmboxes: vmid -> mailbox;
    current: vmid;
}.

Inductive spci_value_func : Set :=
    | HF_SPCI_RUN_WAIT_FOR_INTERRUPT
    | SPCI_MSG_WAIT_32
    | SPCI_INTERRUPT_32.

Record spci_value : Set := SPCI_Value {
	func: spci_value_func;
	arg1: nat;
	arg2: nat;
	arg3: nat;
	arg4: nat;
	arg5: nat;
	arg6: nat;
	arg7: nat;
}.
