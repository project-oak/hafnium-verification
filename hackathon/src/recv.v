Require Import Mailbox.global_state.
Require Import Mailbox.utils.
Require Import Mailbox.switch_to_primary.

(*-------------------------------------------------------------------------*)
(* interrupted                                                             *)
(*-------------------------------------------------------------------------*)
(* Without modeling vCPU, we cannot implement interrupted(). *)

Definition interrupted (vcpu_id: vmid): bool :=
    true.    

(*-------------------------------------------------------------------------*)
(* recv                                                                    *)
(*-------------------------------------------------------------------------*)
(* hsk: corresponds to api_spci_msg_recv() in C implementation.
 * (1) If primary VM => return SPCI_NOT_SUPPORTED error
 * (2) If there was a message => change mailbox state to MAILBOX_STATE_READ. Return SPCI_MSG_SEND_32 + alpha
 * (3) If nonblocking => return SPCI_RERY error
 * (4) If there was an interrupt => return SPCI_INTERRUPTED error
 * (5) In all other cases, block until receiving a message
   HSK-TODO: How is a blocked VM eventually woken up? *)

(* aferr: Note that AFAICT this call does not actually do anything with the data
 * in the reveive buffer. It just changes the mailbox state on a successful call. 
 * Presumably the expectation is that between the recv call and the clear call 
 * the caller will manually copy the data out of the receive buffer. *)

(* hsk: what do we want to do with the return code?
 * In the C implementation, return code is more than error code.
 * For the hackathon, we may not need to model it precisely. *)

(* hsk: is there really anything that we can abstract way in this function? *)

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
            | true => if interrupted cur
                        then (s, recvRetInt)
                        else ((switchToPrimary s VCPU_STATE_BLOCKED_MAILBOX), recvRetInt)
        end
    end.

