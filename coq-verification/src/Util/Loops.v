Require Import Coq.Lists.List.
Require Import Hafnium.Util.Tactics.

Definition continue := false.
Definition break := true.
Definition while_loop
           {state : Type}
           {max_iterations : nat} (* limit # iterations to prove termination *)
           (cond : state -> bool)
           (start : state)
           (body : state -> state * bool)
  : state :=
  fst (
      fold_right
        (fun _ (before : state * bool) =>
           let '(s, loop_done) := before in
           if (loop_done || negb (cond s))%bool
           then (s, break) (* exit loop, keep old state *)
           else body s)
        (start, continue)
        (seq 0 max_iterations)).

Lemma while_loop_invariant {state} (P : state -> Prop) max_iterations cond body :
  forall start,
    (forall s, cond s = true -> P s -> P (fst (body s))) ->
    P start ->
    P (@while_loop _ max_iterations cond start body).
Proof.
  cbv [while_loop]. generalize (seq 0 max_iterations) as l.
  induction l;
    repeat match goal with
           | _ => progress cbn [fold_right fst snd]
           | _ => progress basics
           | |- context [let '(_,_) := ?x in _] =>
             rewrite (surjective_pairing x)
           | _ => break_match
           | _ => inversion_bool
           | _ => solver
           end.
Qed.
