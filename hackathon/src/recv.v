Require Import Mailbox.global_state.
Require Import Mailbox.utils.
Require Import Mailbox.switch_to_primary.

(*-------------------------------------------------------------------------*)
(* Recv                                                                    *)
(*-------------------------------------------------------------------------*)
(* aferr: Note that AFAICT this call does not actually do anything with the data
 * in the reveive buffer. It just changes the mailbox state on a successful call. 
 * Presumably the expectation is that between the recv call and the clear call 
 * the caller will manually copy the data out of the receive buffer. *)

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

