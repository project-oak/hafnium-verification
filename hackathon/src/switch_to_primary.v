Require Import Mailbox.global_state.
Require Import Mailbox.utils.

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
Definition arch_timer_enabled_current(s: hfstate): bool := false.
Definition remaining_ns_current(s: hfstate): nat := 0.
Definition SPCI_SLEEP_INDEFINITE: nat := 0. (* it's really 0xffffffffffffffff*)

(* this is the inner part of switchToPrimary for when (func primary_ret) is
* HF_SPCI_RUN_WAIT_FOR_INTERRUPT or SPCI_MSG_WAIT_32 *)
Definition handlePrimaryRet(s: hfstate)(primary_ret: spci_value): spci_value:= 
    if arch_timer_enabled_current s then
        if Nat.eqb (remaining_ns_current s) 0 then
            (updarg (updfun primary_ret SPCI_INTERRUPT_32) 2 0)
            else (updarg primary_ret 2 (remaining_ns_current s))
    else updarg primary_ret 2 SPCI_SLEEP_INDEFINITE.

Definition switchToPrimary(s: hfstate)(code: vcpuState)(primary_ret:
    spci_value): hfstate := s.
    (*
    match func primary_ret with
        | HF_SPCI_RUN_WAIT_FOR_INTERRUPT
        | SPCI_MSG_WAIT_32
        | SPCI_INTERRUPT_32
    end.
*)

