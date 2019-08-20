(*
 * Copyright 2019 Jade Philipoom
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Hafnium.Util.List.
Require Import Hafnium.Util.Tactics.

Definition continue := false.
Definition break := true.
Definition while_loop'
           {state : Type}
           (max_iterations : nat) (* limit # iterations to prove termination *)
           (cond : state -> bool)
           (start : state)
           (body : state -> state * bool)
  : state * bool :=
  fold_right
    (fun _ (before : state * bool) =>
       let '(s, loop_done) := before in
       if (loop_done || negb (cond s))%bool
       then (s, break) (* exit loop, keep old state *)
       else body s)
    (start, continue)
    (seq 0 max_iterations).
Definition while_loop
           {state} {max_iterations} cond start body : state :=
  fst (@while_loop' state (S max_iterations) cond start body).

Lemma while_loop_invariant {state} (P : state -> Prop) max_iterations cond body :
  forall start,
    (forall s, cond s = true -> P s -> P (fst (body s))) ->
    P start ->
    P (@while_loop _ max_iterations cond start body).
Proof.
  cbv [while_loop while_loop']. generalize (seq 0 (S max_iterations)) as l.
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

Lemma while_loop'_0 {state} cond (start : state) body :
  while_loop' 0 cond start body = (start, continue).
Proof. reflexivity. Qed.

Lemma while_loop'_step {state} max_iterations cond (start : state) body :
  while_loop' (S max_iterations) cond start body =
  if cond start
  then if Bool.bool_dec (snd (body start)) continue
       then while_loop' max_iterations cond (fst (body start)) body
       else body start
  else (start, break).
Proof.
  cbv [while_loop'].
  rewrite seq_snoc, Nat.add_0_l, fold_right_app.
  cbn [fold_right].
  destruct (body start) as [s' loop_done].
  repeat match goal with
           | _ => progress cbn [fold_right fst snd] in *
           | _ => progress cbv [continue break] in *
           | _ => progress basics
           | _ => break_match
           | _ => inversion_bool
           | _ => solver
           | _ => apply fold_right_invariant;
                    try destruct loop_done; basics; solver
           end.
Qed.

Lemma while_loop'_failed {state} max_iterations cond body
      (successful : state -> bool) :
  (forall s, successful s = false -> successful (fst (body s)) = false) ->
  forall start,
    successful start = false ->
    successful (fst (while_loop' max_iterations cond start body)) = false.
Proof.
  cbv [while_loop']. intros.
  apply fold_right_invariant;
    repeat match goal with
           | _ => progress basics
           | _ => progress cbn [fst snd]
           | p : _ * _ |- _ => destruct p
           | _ => break_match
           | _ => solver
           end.
Qed.

Definition sufficient_fuel {state} (ret : state * bool) : Prop :=
  snd ret = break.
Hint Unfold sufficient_fuel.

Lemma while_loop'_completed {state} cond body
      (successful : state -> bool) :
  (forall s, successful (fst (body s)) = true -> snd (body s) = continue) ->
  (forall s, successful s = false -> successful (fst (body s)) = false) ->
  forall max_iterations start,
    sufficient_fuel (while_loop' max_iterations cond start body) ->
    successful (fst (while_loop' max_iterations cond start body)) = true ->
    cond (fst (while_loop' max_iterations cond start body)) = false.
Proof.
  autounfold.
  induction max_iterations;
    repeat match goal with
           | _ => progress basics
           | _ => progress cbn [fst snd] in *
           | _ => rewrite while_loop'_step in * by auto
           | _ => rewrite while_loop'_0 in * by auto
           | _ => break_match
           | _ => inversion_bool
           | _ => solver
           | _ => cbv [continue break] in *; solver
           | H : (forall s, successful (fst (body s)) = true -> snd (body s) = continue),
                 H'' : _ |- _ => apply H in H''; solver
           end.
Qed.

Definition is_measure {state} (measure: state -> nat) cond body : Prop :=
  (forall s,
      snd (body s) = continue ->
      cond s = true ->
      measure (fst (body s)) < measure s).

Lemma while_loop'_sufficient_fuel {state} cond body measure :
  is_measure measure cond body ->
  forall max_iterations start,
    measure start < max_iterations ->
    sufficient_fuel (@while_loop' state max_iterations cond start body).
Proof.
  cbv [is_measure sufficient_fuel].
  induction max_iterations;
    repeat match goal with
           | _ => progress basics
           | _ => progress cbn [fst snd] in *
           | _ => rewrite while_loop'_step in * by auto
           | _ => rewrite while_loop'_0 in * by auto
           | _ => break_match
           | _ => inversion_bool
           | _ => solver
           | _ => destruct (snd (body start)); solver
           | H : (forall s, snd (body s) = continue -> _ -> _ ),
                 H' : _ |- _ => apply H in H'; try apply IHmax_iterations; solver
           end.
Qed.

Lemma while_loop_completed_measure {state} max_iterations cond body
      (successful : state -> bool) measure start:
  is_measure measure cond body ->
  (forall s, successful (fst (body s)) = true -> snd (body s) = continue) ->
  (forall s, successful s = false -> successful (fst (body s)) = false) ->
  (measure start <= max_iterations) ->
  successful (@while_loop _ max_iterations cond start body) = true ->
  cond (@while_loop _ max_iterations cond start body) = false.
Proof.
  cbv [while_loop]; basics.
  eapply while_loop'_completed; eauto; [ ].
  eapply while_loop'_sufficient_fuel; solver.
Qed.

Lemma while_loop'_proper_cond {state} max_iterations body
      cond cond' :
  (forall s, cond s = cond' s) ->
  forall start,
    @while_loop' state max_iterations cond start body =
    @while_loop' state max_iterations cond' start body.
Proof.
  intro Hcond_eq.
  induction max_iterations; intros;
    rewrite ?while_loop'_step, ?while_loop'_0 by auto;
    rewrite ?Hcond_eq, ?IHmax_iterations by auto;
    solver.
Qed.

Lemma while_loop_proper_cond {state} max_iterations body
      cond cond' :
  (forall s, cond s = cond' s) ->
  forall start,
    @while_loop state max_iterations cond start body =
    @while_loop state max_iterations cond' start body.
Proof. cbv [while_loop]; intros; erewrite while_loop'_proper_cond; eauto. Qed.

Lemma while_loop'_increments {state} body
      (value : state -> nat) (end_value : nat) :
  (* the value increments will not skip over the end value *)
  (forall s, snd (body s) = continue -> value s < end_value ->
             value (fst (body s)) <= end_value) ->
  forall max_iterations start,
    sufficient_fuel
      (while_loop' max_iterations (fun s => value s <? end_value) start body) ->
    value start <= end_value ->
    while_loop' max_iterations (fun s => value s <? end_value) start body =
    while_loop' max_iterations (fun s => negb (value s =? end_value)) start body.
Proof.
  intro.
  induction max_iterations;
    repeat match goal with
           | _ => progress basics
           | _ => progress cbn [fst snd] in *
           | _ => rewrite while_loop'_step in * by auto
           | _ => rewrite while_loop'_0 in * by auto
           | _ => break_match
           | _ => inversion_bool
           | _ => solver
           end.
Qed.

Lemma while_loop_lt_is_measure {state} body
      (value : state -> nat) (end_value : nat) :
  (forall s, snd (body s) = continue -> value s < value (fst (body s))) ->
  is_measure (fun s => end_value - value s) (fun s => value s <? end_value) body.
Proof.
  cbv [is_measure];
    repeat match goal with
           | _ => progress basics
           | |- _ <-> _ => split
           | |- _ = false => apply Nat.ltb_ge
           | _ => inversion_bool
           | _ => solver
           | H : (forall s, snd (body s) = continue -> _ ),
                 H' : _ |- _ => apply H in H'; solver
           end.
Qed.

(* If a while loop's termination condition is that a particular measure of the
   state passes a goal value, and the measure is incremented such that the goal
   value will not be skipped over, it is equivalent to encode the while loop as
   terminating when the state value equals the goal value, not when it's greater
   than or equal. This is useful because it lets us declare that, when the loop
   terminates, the final state has the exact goal value. *)
Lemma while_loop_increments {state} max_iterations body
      (value : state -> nat) (end_value : nat) :
  (* the value increments monotonically increase *)
  (forall s, snd (body s) = continue -> value s < value (fst (body s))) ->
  (* the value increments will not skip over the end value *)
  (forall s, snd (body s) = continue -> value s < end_value ->
             value (fst (body s)) <= end_value) ->
  forall start,
    value start <= end_value ->
    end_value - value start <= max_iterations ->
    @while_loop _ max_iterations (fun s => value s <? end_value) start body =
    @while_loop _ max_iterations (fun s => negb (value s =? end_value)) start body.
Proof.
  cbv [while_loop]; intros. apply f_equal.
  eapply while_loop'_increments; eauto; [ ].
  eapply while_loop'_sufficient_fuel;
    eauto using while_loop_lt_is_measure;
    solver.
Qed.

(* puts [while_loop_increments] and [while_loop_completed] together to prove that
   the final "value" of the loop state will be exactly equal to the end value. *)
Lemma while_loop_end_exact {state} max_iterations body
      (successful : state -> bool) (value : state -> nat) (end_value : nat)
      (cond : state -> bool) :
  (forall s, cond s = (value s <? end_value)) ->
  (forall s, successful (fst (body s)) = true -> snd (body s) = continue) ->
  (forall s, successful s = false -> successful (fst (body s)) = false) ->
  (forall s, snd (body s) = continue -> value s < value (fst (body s))) ->
  (forall s, snd (body s) = continue -> value s < end_value ->
             value (fst (body s)) <= end_value) ->
  forall start,
    value start <= end_value ->
    end_value - value start <= max_iterations ->
    successful (@while_loop _ max_iterations cond start body) = true ->
    value (@while_loop _ max_iterations cond start body) = end_value.
Proof.
  intros.
  erewrite while_loop_proper_cond
    with (cond':=fun s => value s <? end_value) in * by auto.
  rewrite while_loop_increments in * by auto.
  match goal with
  | H : successful _ = true |- _ =>
    eapply while_loop'_completed in H; eauto
  end; [ repeat inversion_bool; solver | ].
  rewrite <-while_loop'_increments; eauto;
    eapply while_loop'_sufficient_fuel;
    eauto using while_loop_lt_is_measure; solver.
Qed.

Lemma while_loop_completed {state} max_iterations cond body
      (successful : state -> bool) value end_value start:
  (forall s, cond s = (value s <? end_value)) ->
  (forall s, successful (fst (body s)) = true -> snd (body s) = continue) ->
  (forall s, successful s = false -> successful (fst (body s)) = false) ->
  (forall s, snd (body s) = continue -> value s < value (fst (body s))) ->
  end_value - value start <= max_iterations ->
  successful (@while_loop _ max_iterations cond start body) = true ->
  cond (@while_loop _ max_iterations cond start body) = false.
Proof.
  intros.
  eapply while_loop_completed_measure with
      (measure:=fun s => end_value - value s); try eassumption.
  cbv [is_measure]; intros.
  repeat match goal with
         | H : (forall s, snd (body s) = continue -> _),
               H' : _ |- _ => apply H in H'
         | H : forall s, cond s = _ |- _ => progress rewrite H in *
         | H : (_ <? _) = true |- _ => apply Nat.ltb_lt in H
         | _ => solver
         end.
Qed.

Lemma while_loop_noop {state} max_iterations cond start body :
  cond start = false ->
  @while_loop state max_iterations cond start body = start.
Proof.
  cbv [while_loop]; intros. rewrite while_loop'_step.
  repeat break_match; solver.
Qed.

Definition is_while_loop_value {state} value end_value cond body : Prop :=
  (* value is < end_value iff cond is true *)
  (forall s : state, cond s = (value s <? end_value))
  (* ...and value decreases monotonically *)
  /\ (forall s : state, snd (body s) = continue -> value s < value (fst (body s))).

Definition is_while_loop_success {state} successful body : Prop :=
  (* the success metric never goes from false to true *)
  (forall s : state, successful s = false -> successful (fst (body s)) = false)
  (* ...and success implies that the loop continues *)
  /\ (forall s : state, successful (fst (body s)) = true -> snd (body s) = continue).

Definition is_while_loop_invariant
           {state} (inv : state -> Prop) successful cond body : Prop :=
  (* the loop only breaks when the continuation condition or success condition
       is false anyway -- this guarantees that if successful = true, the loop
       completed *)
  (forall s, cond s = true -> inv s ->
             snd (body s) = continue
             \/ cond (fst (body s)) = false
             \/ successful (fst (body s)) = false)
  (* ...and invariant holds over loop *)
  /\ (forall s : state, cond s = true -> inv s -> inv (fst (body s))).

Lemma while_loop_invariant_strong
      {state} (inv P : state -> Prop) (successful : state -> bool)
      (value : state -> nat) (end_value : nat)
      max_iterations cond body start :
  is_while_loop_value value end_value cond body ->
  is_while_loop_success successful body ->
  is_while_loop_invariant inv successful cond body ->
  (* we have enough fuel *)
  end_value - value start <= max_iterations ->
  (* invariant holds at start *)
  inv start ->
  (* invariant implies conclusion *)
  (forall s, inv s -> (cond s = false \/ successful s = false) -> P s) ->
  P (while_loop (max_iterations:=max_iterations) cond start body).
Proof.
  cbv [is_while_loop_value is_while_loop_success is_while_loop_invariant]; basics.
  match goal with H : _ |- _ => apply H end.
  { apply while_loop_invariant; eauto. }
  { match goal with |- context [successful ?s] =>
                    case_eq (successful s); basics; try solver end.
    left. eapply while_loop_completed; eauto. }
Qed.
