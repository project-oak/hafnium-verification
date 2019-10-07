Require Import ListSet.

(*-------------------------------------------------------------------------*)
(* Hafnium State                                                           *)
(*-------------------------------------------------------------------------*)
(*aferr: idk if maybe already exists*)
Inductive maybe (t: Set) : Set :=
  | Some: t -> maybe t
  | None: maybe t.

Definition msg : Set := nat.
Inductive vmid : Set :=
  | Primary: vmid
  | Secondary : nat -> vmid.

Definition wlist := list vmid.
Record mailbox : Set := Mailbox {
    sendb: maybe msg; recvb: maybe msg; waiters: wlist
}.

Eval simpl in (Mailbox (Some nat 3) (Some nat 4) nil).

Record hfstate: Set := HFState {
    vmboxes: vmid -> mailbox;
    next: vmid
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
            (* receiver mailbox not empty, so we need to either
            * notify or block *)
    end.


