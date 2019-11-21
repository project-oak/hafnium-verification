Require Import Mailbox.global_state.
Require Import Mailbox.utils.
Require Import Mailbox.switch_to_primary.

(*-------------------------------------------------------------------------*)
(* writable_get                                                            *)
(*-------------------------------------------------------------------------*)

vm <- current->vm
if(vm->mailbox.read_list is empty) return -1
entry <- remove the first entry in the ready list
get ID from the entry
return ID

