Require Import ListSet.
Require Import Coq.Lists.List.
Require Import Mailbox.global_state.

(*-------------------------------------------------------------------------*)
(* Utilities                                                               *)
(*-------------------------------------------------------------------------*)
Definition eqid (x y: vmid): bool :=
    match (x, y) with
        | (Primary, Primary) => true
        | (Secondary xx, Secondary yy) => Nat.eqb xx yy
        | (_, _) => false
    end.

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
        
