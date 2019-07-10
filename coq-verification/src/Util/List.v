Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Hafnium.Util.Tactics.
Import ListNotations.

(* perform inversion on list-based inductives in hypotheses *)
Ltac invert_list_properties :=
  repeat match goal with
         | H : Exists _ (_ :: _) |- _ => invert H
         | H : Exists _ [] |- _ => invert H
         | H : Forall _ (_ :: _) |- _ => invert H
         | H : ForallOrdPairs _ (_ :: _) |- _ => invert H
         | H : In _ (_ :: _) |- _ => invert H
         | H : In _ [] |- _ => invert H
         end.

(* tell [auto] to try applying basic properties of [In] *)
Local Hint Resolve in_cons in_eq.

(* Proofs about [length] *)
Section Length.
  Lemma nil_length {A} : @length A [] = 0.
  Proof. reflexivity. Qed.
  Lemma cons_length {A} (a : A) l : length (a :: l) = S (length l).
  Proof. reflexivity. Qed.
End Length.
(* add all length lemmas to the new rewrite database [push_length] *)
Hint Rewrite @nil_length @cons_length : push_length.
Hint Rewrite @seq_length @repeat_length @rev_length @map_length @firstn_length
     @app_length @split_length_l @prod_length @split_length_r  @combine_length
  : push_length.

(* Proofs about [repeat] *)
Section Repeat.
  Context {A : Type} (a : A) (n : nat).

  Lemma in_repeat a' : In a' (repeat a n) -> a' = a.
  Proof.
    induction n; cbn [repeat];
      repeat match goal with
             | _ => progress basics
             | _ => progress invert_list_properties
             | _ => solver
             end.
   Qed.
End Repeat.

(* Proofs about [remove] *)
Section Remove.
  Context {A} (eq_dec : forall x y : A, {x = y} + {x <> y}).

  Lemma In_remove x y ls : In y (remove eq_dec x ls) -> In y ls.
  Proof.
    induction ls; cbn [remove];
      repeat match goal with
             | _ => progress basics
             | _ => progress break_match
             | _ => progress invert_list_properties
             | _ => solver
             end.
  Qed.

  Lemma remove_length_le x ls : length (remove eq_dec x ls) <= length ls.
  Proof.
    induction ls; cbn [remove];
      repeat match goal with
             | _ => progress break_match
             | _ => progress autorewrite with push_length
             | _ => solver
             end.
  Qed.

  (* hint for the below proof *)
  Local Hint Resolve Lt.lt_n_S.

  Lemma remove_length_lt x ls :
    In x ls -> length (remove eq_dec x ls) < length ls.
  Proof.
    induction ls; cbn [remove];
      repeat match goal with
             | _ => progress basics
             | _ => progress break_match
             | _ => progress invert_list_properties
             | _ => progress autorewrite with push_length
             | |- context [length (remove _ ?x ?ls)] =>
               pose proof (remove_length_le x ls); solver
             | _ => solver
             end.
  Qed.
End Remove.

Section NthDefault.
  Context {A} (d : A).

  Lemma nth_default_nil i : nth_default d [] i = d.
  Proof. destruct i; reflexivity. Qed.

  Lemma nth_default_cons i a ls :
    nth_default d (a :: ls) (S i) = nth_default d ls i.
  Proof. reflexivity. Qed.

  Lemma nth_default_in_bounds i ls :
    nth_default d ls i <> d -> i < length ls.
  Proof.
    generalize dependent ls; induction i; destruct ls;
      repeat match goal with
             | _ => progress basics
             | _ => progress autorewrite with push_length
             | _ => rewrite nth_default_cons in *
             | _ => solver
             | _ => solve [auto using Lt.lt_n_S]
             end.
  Qed.
End NthDefault.
Hint Rewrite @nth_default_nil @nth_default_cons : push_nth_default.

Section FoldRight.
  Context {A B : Type}.

  Lemma fold_right_invariant (P : B -> Prop) (f : A -> B -> B) b ls :
    (forall a b, P b -> P (f a b)) ->
    P b ->
    P (fold_right f b ls).
  Proof.
    generalize dependent b; induction ls; intros;
      cbn [fold_right]; eauto.
  Qed.
End FoldRight.

(* Proofs about [firstn] and [skipn] *)
Section FirstnSkipn.
  Context {A : Type}.

  Lemma in_firstn (a : A) ls : forall i, In a (firstn i ls) -> In a ls.
  Proof.
    induction ls; destruct i;
      repeat match goal with
             | _ => progress basics
             | _ => progress invert_list_properties
             | _ => rewrite firstn_O in *
             | _ => rewrite firstn_cons in *
             | _ => solver
             end.
  Qed.

  Lemma in_skipn (a : A) ls : forall i, In a (skipn i ls) -> In a ls.
  Proof.
    induction ls; destruct i;
      repeat match goal with
             | _ => progress invert_list_properties
             | _ => solver
             end.
  Qed.

  Lemma skipn_nil i : @skipn A i [] = [].
  Proof. destruct i; reflexivity. Qed.
  Lemma skipn_cons i (a : A) ls : skipn (S i) (a :: ls) = skipn i ls.
  Proof. reflexivity. Qed.

  Lemma skipn_nth_default_cons (d : A) i ls :
    i < length ls ->
    skipn i ls = nth_default d ls i :: skipn (S i) ls.
  Proof.
    generalize dependent ls; induction i; destruct ls;
      repeat match goal with
             | _ => progress basics
             | _ => progress autorewrite with push_length push_nth_default in *
             | _ => rewrite skipn_cons
             | _ => apply IHi; lia
             | _ => solver
             end.
  Qed.
End FirstnSkipn.

(* autorewrite databases for [firstn] and [skipn] *)
Hint Rewrite @firstn_O @firstn_nil @firstn_cons : push_firstn.
Hint Rewrite @skipn_nil @skipn_cons : push_skipn.

(* Proofs about setting the nth element of a list. *)
Section SetNth.
  Context {A : Type}.

  (* set the ith element of a list *)
  Definition set_nth (ls : list A) (a : A) (i : nat) : list A :=
    firstn i ls ++ a :: skipn (S i) ls.

  Lemma in_set_nth_eq ls : forall a i, In a (set_nth ls a i).
  Proof.
    cbv [set_nth]; induction ls;
      repeat match goal with
             | _ => progress basics
             | _ => rewrite in_app_iff
             | _ => solver
             end.
  Qed.

  Lemma in_set_nth_iff ls a a' i :
    i < length ls ->
    In a' (set_nth ls a i) <->
    (In a' (firstn i ls) \/ In a' (skipn (S i) ls) \/ a' = a).
  Proof.
    cbv [set_nth]; induction ls;
      repeat match goal with
             | _ => progress basics
             | _ => progress invert_list_properties
             | _ => rewrite in_app_iff
             | _ => split
             | _ => solver
             end.
  Qed.
End SetNth.

(* Proofs about "list qualifiers" like [Forall] and [Exists] *)
Section ListQualifiers.

  (* tactic to simplify foals with [Forall] or [ForallOrdPairs] *)
  Local Ltac crush_forall' :=
    repeat match goal with
           | _ => progress basics
           | _ => rewrite app_nil_l in *
           | _ => rewrite <-app_comm_cons in *
           | H : Forall _ (_ :: _) |- _ => invert H
           | |- Forall _ (_ :: _) => apply Forall_cons
           | H : ForallOrdPairs _ (_ :: _) |- _ => invert H
           | |- ForallOrdPairs _ (_ :: _) => apply FOP_cons
           | _ => split
           | _ => solve [auto using FOP_nil]
           | _ => tauto
           end.

  Lemma Forall_app_iff {A} (P : A -> Prop) ls1 ls2 :
    Forall P (ls1 ++ ls2) <-> (Forall P ls1 /\ Forall P ls2).
  Proof. induction ls1; crush_forall'. Qed.

  (* update [crush_forall'] to include Forall_app_iff *)
  Local Ltac crush_forall :=
    repeat match goal with
           | H : _ |- _ => rewrite Forall_app_iff in H
           | |- Forall _ (_ ++ _) => apply Forall_app_iff
           | _ => crush_forall'
           end.

  (*** Some proofs about [ForallOrdPairs] ***)

  Lemma FOP_app_iff {A} (P : A -> A -> Prop) ls1 ls2 :
    ForallOrdPairs P (ls1 ++ ls2) <->
    (ForallOrdPairs P ls1
     /\ ForallOrdPairs P ls2
     /\ Forall (fun x => Forall (P x) ls2) ls1).
  Proof. induction ls1; crush_forall. Qed.
  Lemma FOP_app_cons_iff {A} (P : A -> A -> Prop) ls1 a ls2 :
    ForallOrdPairs P (ls1 ++ a :: ls2) <->
    (ForallOrdPairs P ls1
     /\ ForallOrdPairs P ls2
     /\ Forall (P a) ls2
     /\ Forall (fun x => P x a) ls1
     /\ Forall (fun x => Forall (P x) ls2) ls1).
  Proof. induction ls1; crush_forall. Qed.
  Lemma FOP_app_split {A} (P : A -> A -> Prop) ls1 ls2 :
    ForallOrdPairs P (ls1 ++ ls2) ->
    (ForallOrdPairs P ls1 /\ ForallOrdPairs P ls2).
  Proof. induction ls1; crush_forall. Qed.
  Lemma FOP_app_cons_l {A} (P : A -> A -> Prop) ls1 a ls2 :
    ForallOrdPairs P (ls1 ++ a :: ls2) ->
    Forall (fun x => P x a) ls1.
  Proof. induction ls1; crush_forall. Qed.
  Lemma FOP_app_cons_r {A} (P : A -> A -> Prop) ls1 a ls2 :
    ForallOrdPairs P (ls1 ++ a :: ls2) -> Forall (P a) ls2.
  Proof.
    let H := fresh in
    intro H; apply FOP_app_split in H;
      let X := fresh in
      destruct H as [? X]; inversion X; subst; auto.
  Qed.

  (*** Some proofs about [Forall] ***)

  Lemma Forall_impl2 {A} (P1 P2 Q : A -> Prop) ls :
    (forall a, P1 a -> P2 a -> Q a) ->
    Forall P1 ls -> Forall P2 ls -> Forall Q ls.
  Proof. intros; rewrite Forall_forall in *. auto. Qed.
  Lemma Forall_sym {A} (f : A -> A -> Prop)
        (Hsym : forall a1 a2, f a1 a2 -> f a2 a1) ls a :
    Forall (fun x => f x a) ls -> Forall (f a) ls.
  Proof. intros; rewrite Forall_forall in *. auto. Qed.

End ListQualifiers.

(* Define a notation for indexing into lists. Coq requires a default element to
   be passed in case the index is out of bounds; in order not to have to repeat
   this element everywhere, we create a class and will later globally instantiate
   it for certain types. *)
Class OutOfBoundsElement T := { oob_value : T }.
Definition nth_default_oobe
           {T} {oobe : OutOfBoundsElement T} (ls : list T) (i : nat) : T :=
  nth_default oob_value ls i.

(* populate the list_quals hint database *)
Hint Resolve FOP_nil FOP_cons Forall_nil Forall_forall
  : list_quals.
Hint Resolve in_or_app in_cons in_eq : list_quals.

(* simplify goals with list qualifiers *)
Ltac simpl_list_qualifiers :=
  repeat match goal with
         | _ => rewrite Exists_nil in *
         | _ => apply Forall_cons
         | H : _ |- _ => rewrite Forall_app_iff in H
         | |- Forall _ (_ ++ _) => apply Forall_app_iff
         | _ => apply FOP_cons
         | _ => solve [auto with list_quals]
         end.
