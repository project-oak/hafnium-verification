Require Import ListSet.
Require Import Coq.Lists.List.

(* 
Noninterference is too strict to prove about Hafnium because we have 
intentional information release. We may also have side channels that we cannot
address by changing the hypervisor (for performance or other reasons).

The high-level idea here is to prove a weakening of noninterference by:
-- annotating the spec with ghost state representing information flow labels
-- adding ghost state annotations representing "escape hatches" that 
    permit exceptions to noninterference.

Here labels represent the secrecy of different participants in the system.

Label syntax:
{P} The primary VM 
{S n} Secondary VM with identifier n 
{l1 join l2} The upper bound on the secrecy of two labels l1, l2.
    (it may contain information from either l1 or l2 or both)
{l1 meet l2} The lower bound on the secrecy of two labels l1, l2.
    (either l1 or l2 can see this information)
{top} The top label -> secret to everyone
{bot} The bottom label -> public to everyone

Declassification (escape hatch) syntax:
declassify( <expression>, <label>)
    -- this means "weaken" the label of <expression> to <label>

Checking information flow can work like a type system:
Assume e1, e2, e3 have labels l1, l2, l3
 - e1 op e2                             has label {l1 join l2}
 - let x := e1                          x must have a label at least as secret as l1
 - f( x: Type {l3}) : Type {l1} := e1   is well-labeled
Branching can introduce "implicit flows". These are prevented by assocating a
label called "pc" for branch conditionals:
 - let x := if(e1) then e2 else e3      x must have at least {l1 join l2 join l3}

Without any declassify expressions, we can prove a strong security condition:
 - Assume the spec is composed of functions that mutate state: 
    s' = f(s)        s' is the new state and s is the old one.
 - traces t are sequences of states, t[n] is the nth element of the trace
 - s1 =l s2    --> relates s1 and s2 if all the parts with label l are equal
 - t1 =l t2    --> relates t1 and t2 if they "appear the same" to label l
            (this definition can be more complicated than for states)
    Then we could try to prove:
        t1[0] =l t2[0] ==> t1 =l t2
    Meaning if the initial states "look the same to l" then so should the 
    whole execution

This is too strong once we add in declassify expressions. We can make up for
declassify expressions by adding in events to traces that represent declassify
expressions. The idea is that if in both executions:
    - the "l" parts of the initial states are the same 
    - and if all secrets revealed to "l" by downgrading during the execution 
        are the same
    - then the sequence of states should look the same.

We can (semi-)formalize this:
Declassify event syntax d ::=
    | Empty                       No event  
    | x : l2 <-- n : l1           Value n labeled l1 declassified to x labeled l2

Here is a weaker condition we can try to prove:
    - Traces are now sequences of pairs of states and events d: 
        (s1, d1), (s2, d2), ..., (sn, dn)
    - d1 =l d2          two events "look the same to l" if:
            - l can see the recipient label (l2) and the events are equal
            - l cannot see the recipient label
    - t1 ~l  t2     just the event parts of the traces are the same
    - t1 ==l t2     just the state parts of the traces are the same
    Now we can try to prove:
        t1[0] =l t2[0] /\ t1 ~l t2 ==> t1 ==l t2
        
This security condition is explored by adding ghost annotations to this small
spec of Hafnium. 
Here the annotations: x (*{l}*) next to variables are meant to represent labels
*)

(*-------------------------------------------------------------------------*)
(* Hafnium State                                                           *)
(*-------------------------------------------------------------------------*)

Inductive maybe (t: Set) : Set :=
  | Some: t -> maybe t
  | None: maybe t.

(* TODO make this an uninterpreted finite set *)
Definition msg : Set := nat.

Inductive vmid : Set :=
  | Primary: vmid            (*{bot}*)
  | Secondary : nat -> vmid. (*{bot}*)

Definition wlist := list vmid.

Inductive mboxState : Set := 
    | Read : mboxState  (*{bot}*) 
    | Recv : mboxState  (*{bot}*) 
    | Empt : mboxState  (*{bot}*).

(*aferr: it looks like we want label parameters.*)
(* use the syntax {param: l} -> Set to declare a Set with label parameter l*)
(* use the normal function application syntax to apply label parameters: e.g.
* (mailbox l1) applies l1 as the parameter *)
Record mailbox : (* {param: l} ->*) Set  := Mailbox {
    state: mboxState;    (*{bot}*) 
    sendb: maybe msg;    (*{l}*) 
    recvb: maybe msg;    (*{l}*)
    waiters: wlist       (*{bot}*)
}.
(* aferr: here the state and list of waiters need to be public because all
* other VMs can see them by trying to send messages to this mailbox *)

Eval simpl in (Mailbox Read (Some nat 3) (Some nat 4) nil).

(*TODO model of VCPUs *)
Record hfstate: Set := HFState {
	(* TODO eventually need more complete model of VM state. Reachable memory,
    * etc.*)
    vmboxes: vmid -> mailbox (* vmid *);    (*applying label parameter vmid*)
    current: vmid;  (* {bot} *)
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
        
(*-------------------------------------------------------------------------*)
(* HVCs                                                                    *)
(*-------------------------------------------------------------------------*)

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

(*-------------------------------------------------------------------------*)
(* Send                                                                    *)
(*-------------------------------------------------------------------------*)
Definition sendargs : Set := nat.
(* TODO learn how to make uninterpreted set declarations *)

(* Returns true when HVC would error instead of executing. *)
Inductive sendRet: Set :=
    | sendRetError
    | sendRetSucc
    | sendRetBusy.

(* TODO *)
Definition sendErrs (s: hfstate)(args: sendargs): bool := false.

(* sendArchitected is how page permissions are changed. 
*  It is a special case of the send HVC (depending on args) *)
Definition doSendArchitected (args : sendargs): bool := false. (* TODO *)
Definition sendArchitected (s: hfstate) (to from : vmid) (args: sendargs):
    (hfstate * sendRet) :=
    (s, sendRetError). (* TODO *)

Definition doNotify (args: sendargs) : bool := false. (* TODO *)


(*aferr: the label structure of hfstate is defined with the
annotations in the definition of hfstate.
*)
(*the arguments are labeled with the VM making the HVC*)
Definition send (s: hfstate) (to: vmid (*{s.hfstate.current}*) ) 
    (args: sendargs (* {s.hfstate.current} *)):
  (hfstate * sendRet) :=
    let from := current s in
    let oldto := (vmboxes s) to in
    let oldfrom := (vmboxes s) from in
    if sendErrs s args then (s, sendRetError)
    else match state oldto with 
        | Empt => 
            (*aferr: because this is a branch depending on args which has label
            {s.hfstate.current} and the code below the branch influences values
            with the {bot} label, we need to insert a declassify to
            "typecheck". The same is true for the choice of "to" because if it
            is is the primary, we context switch.
            *)
            if (*declassify ( *)doSendArchitected args (*, {bot}) *) 
                then sendArchitected s to from args
                else let toprime := Mailbox Recv (sendb oldto)
                    (*aferr: this declassify expression we expect. This is
                    * needed because we are sending a value to the recipient {to} *)
                    (sendb (* declassify( *) oldfrom (*, {to} *)) (waiters oldto) in
                    let sprime := updvmbox s to toprime in
                    if (*declassify *( *) eqid Primary to (*, {bot}) *) then 
						(switchToPrimary sprime VCPU_STATE_READY,
                        	sendRetSucc)
                    else (sprime, sendRetSucc)
        | _ => 
            if (*declassify ( *) doNotify args (*, {bot}) *) then 
                let toprime := updwaiter oldto from in
                (updvmbox s to toprime, sendRetBusy)
            else (s, sendRetBusy)
            (* receiver mailbox not empty, so we need to either
            * notify or block *)
    end.
(*
    Each declassify expression would correspond to emitting a declassificaiton
    event into the trace. We could also imagine adding these declassification
    event into the type signature, which should expose information release at
    the API level, possibly allowing software built using this API to implement
    defenses to side-channels not addressed in the hypervisor implementation.
*)

(*-------------------------------------------------------------------------*)
(* Recv                                                                    *)
(*-------------------------------------------------------------------------*)
(*aferr: Note that AFAICT this call does not actually do anything with the data
* in the reveive buffer. It just changes the mailbox state on a successful call. Presumably the expectation is that between the recv call and the clear call the caller will manually copy the data out of the receive buffer. *)

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



