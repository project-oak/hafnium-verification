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
(* TODO there must be a better way to write mutators than this!! *)
(* TODO only add to list if it is not already present in the list *)
Definition updwaiter (mb: mailbox)(id: vmid): mailbox :=
    {|
        state := state mb;
        sendb := sendb mb; 
        recvb := recvb mb; 
        waiters := id :: (waiters mb);
        readylist := readylist mb;
    |}.

(* mailbox mutators *)
Definition updready (mb: mailbox)(id: vmid): mailbox :=
    {|
        state := state mb;
        sendb := sendb mb; 
        recvb := recvb mb; 
        waiters := waiters mb;
        readylist := id :: (readylist mb);
    |}.

(* mailbox mutators *)
Definition remwaiter (mb: mailbox): mailbox :=
    {|
        state := state mb;
        sendb := sendb mb; 
        recvb := recvb mb;
        waiters :=
            match waiters mb with 
                | nil => nil
                | cons waiter waiters' => waiters'
            end;
        readylist := readylist mb;
    |}.

(* mailbox mutators *)
Definition updstate (mb: mailbox)(s: mboxState): mailbox :=
    {|
        state := s;
        sendb := sendb mb; 
        recvb := recvb mb; 
        waiters := waiters mb;
        readylist := readylist mb;
    |}.

Definition updfun(v: spci_value)(newval: spci_value_func): spci_value :=
    {|
	    func := newval;
	    arg1 := arg1 v;
	    arg2 := arg2 v;
	    arg3 := arg3 v;
	    arg4 := arg4 v;
	    arg5 := arg5 v;
	    arg6 := arg6 v;
	    arg7 := arg7 v;
    |}.

Definition updarg(v: spci_value)(argchoice: nat)(newval: nat): spci_value :=
    {|
	    func := func v;
	    arg1 := if Nat.eqb argchoice 1 then newval else arg1 v;
	    arg2 := if Nat.eqb argchoice 2 then newval else arg2 v;
	    arg3 := if Nat.eqb argchoice 3 then newval else arg3 v;
	    arg4 := if Nat.eqb argchoice 4 then newval else arg4 v;
	    arg5 := if Nat.eqb argchoice 5 then newval else arg5 v;
	    arg6 := if Nat.eqb argchoice 6 then newval else arg6 v;
	    arg7 := if Nat.eqb argchoice 7 then newval else arg7 v;
    |}.
