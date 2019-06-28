Require Import Coq.omega.Omega.

(* [inversion] with some cleanup afterwards *)
Ltac invert H := inversion H; subst; clear H.

(* simplify the goal in some commonly desired ways *)
Ltac basics :=
  repeat match goal with
         | _ => progress (intros; subst)
         | H : exists _, _ |- _ => destruct H
         | H : _ /\ _ |- _ => destruct H
         | H : _ \/ _ |- _ => destruct H
         | H : ~ (_ \/ _) |- _ => apply Decidable.not_or in H
         | |- ~ (_ \/ _) => intro
         | |- _ /\ _ => split
         | H : Some _ = Some _ |- _ => invert H
         | H : inl _ = inl _ |- _ => invert H
         | H : inr _ = inr _ |- _ => invert H
         end.

(* break up goal into multiple cases *)
Ltac break_match :=
  match goal with
  | |- context [match ?x with _ => _ end] => destruct x
  | H : context [match ?x with _ => _ end] |- _ => destruct x
  end.

(* solves relatively easy goals with some common methods *)
Ltac solver :=
  match goal with
  | _ => tauto
  | _ => solve [eauto]
  | _ => congruence
  | _ => omega
  end.
