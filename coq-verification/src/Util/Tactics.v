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
  | |- context [match ?x with _ => _ end] =>
    match type of x with
    | sumbool _ _ => destruct x
    end
  | H : context [match ?x with _ => _ end] |- _ =>
    match type of x with
    | sumbool _ _ => destruct x
    end
  | |- context [match ?x with _ => _ end] => case_eq x; intro
  | H : context [match ?x with _ => _ end] |- _ =>
    let Heq := fresh in case_eq x; intro Heq; rewrite Heq in H
  end.

(* solves relatively easy goals with some common methods *)
Ltac solver :=
  match goal with
  | _ => tauto
  | _ => solve [eauto]
  | _ => congruence
  | _ => omega
  end.

Ltac inversion_bool :=
  match goal with
  | H : (_ && _)%bool = true |- _ => apply Bool.andb_true_iff in H
  | H : (_ || _)%bool = true |- _ => apply Bool.orb_true_iff in H
  | H : negb _ = true |- _ => apply Bool.negb_true_iff in H
  | H : (_ && _)%bool = false |- _ => apply Bool.andb_false_iff in H
  | H : (_ || _)%bool = false |- _ => apply Bool.orb_false_iff in H
  | H : negb _ = false |- _ => apply Bool.negb_false_iff in H
  | H : (_ <? _) = true |- _ => apply Nat.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Nat.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Nat.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Nat.leb_gt in H
  | H : (_ =? _) = true |- _ => apply Nat.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Nat.eqb_neq in H
  end.
