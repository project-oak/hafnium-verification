
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
