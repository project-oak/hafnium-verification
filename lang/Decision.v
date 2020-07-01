(*
 * Copyright 2020 Jieung Kim
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

Require Import Coq.ZArith.ZArith.
Require Import Coq.PArith.PArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Class Decision (P: Prop) := decide: {P} + {~P}.
Arguments decide P {_}.

Definition isTrue P `{Decision P} :=
  if decide P then true else false.

Definition isTrue_correct P `{Decision P}:
  isTrue P = true -> P.
Proof.
  unfold isTrue.
  destruct (decide P).
  tauto.
  discriminate.
Qed.

Ltac decision :=
  eapply isTrue_correct;
  reflexivity.

Ltac obviously H P :=
  assert (H: P) by decision.

Ltac ensure P :=
  let H := fresh "H" in
  obviously H P; clear H.

(** * Instances *)

Instance decide_true : Decision True.
Proof. hnf; auto. Qed.

Instance decide_false : Decision False.
Proof. hnf; auto. Qed.

Instance decide_Zeq (m n: Z): Decision (m = n) := {decide := Z.eq_dec m n}.
Instance decide_Zle (m n: Z): Decision (m <= n) := {decide := Z_le_dec m n}.
Instance decide_Zlt (m n: Z): Decision (m < n) := {decide := Z_lt_dec m n}.
Instance decide_Zge (m n: Z): Decision (m >= n) := {decide := Z_ge_dec m n}.
Instance decide_Zgt (m n: Z): Decision (m > n) := {decide := Z_gt_dec m n}.
Instance decide_nateq m n: Decision (m = n) := { decide := eq_nat_dec m n }.
Instance decide_natle m n: Decision (m <= n)%nat := { decide := le_dec m n }.
Instance decide_natlt m n: Decision (m < n)%nat := { decide := lt_dec m n }.
Instance decide_poseq (m n: positive): Decision (m = n) := Pos.eq_dec m n.
Instance decide_booleq b1 b2: Decision (b1 = b2) := Bool.bool_dec b1 b2.
Instance decide_Neq (m n: N): Decision (m = n) := {decide := N.eq_dec m n}.

Instance decide_posle (m n: positive): Decision (Pos.le m n).
Proof.
  destruct (Pos.leb m n) eqn:leb.
  - left; apply Pos.leb_le, leb.
  - right; rewrite <- Pos.leb_le, leb; discriminate.
Defined.

Instance and_dec A B: Decision A -> Decision B -> Decision (A /\ B) := {
  decide :=
    match (decide A) with
      | left HA =>
          match (decide B) with
            | left HB => left (conj HA HB)
            | right HnB => right (fun H => HnB (proj2 H))
          end
      | right HnA => right (fun H => HnA (proj1 H))
    end
}.

Instance or_dec A B: Decision A -> Decision B -> Decision (A \/ B) := {
  decide :=
    match (decide A) with
      | left HA => left (or_introl HA)
      | right HnA =>
        match (decide B) with
          | left HB => left (or_intror HB)
          | right HnB => right (fun HAB => match HAB with
                                             | or_introl HA => HnA HA
                                             | or_intror HB => HnB HB
                                           end)
        end
    end
}.

Program Instance decide_none {A} (a: option A): Decision (a = None) := {
  decide :=
    match a with
      | Some _ => right _
      | None => left _
    end
}.

Program Instance decide_option_eq {A}:
  (forall (x y : A), Decision (x = y)) ->
  (forall (x y : option A), Decision (x = y)) := 
  fun H x y =>
    match x, y with
      | Some x, Some y =>
        match decide (x = y) with
          | left H => left (f_equal _ H)
          | right H => right _
        end
      | None, None =>
        left eq_refl
      | _, _ =>
        right _
    end.
Obligation 4.
intros contra; destruct x eqn: ?; destruct y eqn: ?; simpl; try discriminate.
- inversion contra; subst.
  apply (H1 a0 a0); tauto.
- elim H0; tauto.
Qed.

Obligation 5.
split.
- intros [contra _]; inversion contra.
- intros; intros [_ contra]; inversion contra.
Qed.

Obligation 6.
split.
- intros [_ contra]; inversion contra.
- intros; intros [contra _]; inversion contra.
Qed.

(*
Instance decide_option_eq {A}:
  (forall (x y : A), Decision (x = y)) ->
  (forall (x y : option A), Decision (x = y)) := 
  fun H x y =>
    match x, y with
      | Some x, Some y =>
        match decide (x = y) with
          | left H => left (f_equal _ H)
          | right H => right _
        end
      | None, None =>
        left eq_refl
      | _, _ =>
        right _
    end.
Obligations.
  * abstract (injection; eauto).
  * abstract discriminate.
  * abstract discriminate.
Defined.
*)


Program Instance not_dec P `(Pdec: Decision P): Decision (~P) :=
  {
    decide :=
      match Pdec with
        | left _ => right _
        | right _ => left _
      end
  }.

(*
Instance not_dec P `(Pdec: Decision P): Decision (~P) :=
  {
    decide :=
      match Pdec with
        | left _ => right _
        | right _ => left _
      end
  }.
Obligations.
  * abstract tauto.
  * abstract tauto.
Defined.
*)

Program Instance impl_dec P Q `(Pdec: Decision P) `(Qdec: Decision Q): Decision (P->Q) :=
  {
  decide :=
    match Qdec with
    | left HQ => left (fun _ => HQ)
    | right HnQ =>
      match Pdec with
      | left HP => right _
      | right HnP => left _
      end
    end
  }.
Obligation 2.
elim HnP; tauto.
Qed.

(*
Instance impl_dec P Q `(Pdec: Decision P) `(Qdec: Decision Q): Decision (P->Q) :=
  {
  decide :=
    match Qdec with
    | left HQ => left (fun _ => HQ)
    | right HnQ =>
      match Pdec with
      | left HP => right _
      | right HnP => left _
      end
    end
  }.
Proof.
  * abstract tauto.
  * abstract tauto.
Defined.
*)

Section DECIDE_PROD.
  Context A `{Adec: forall x y: A, Decision (x = y)}.
  Context B `{Bdec: forall x y: B, Decision (x = y)}.

  Global Instance decide_eq_pair: forall (x y: A * B), Decision (x = y).
  Proof.
    intros [x1 x2] [y1 y2].
    destruct (decide (x1 = y1)).
    destruct (decide (x2 = y2)).
    left; congruence.
    right; intro H; inversion H; now auto.
    right; intro H; inversion H; now auto.
  Defined.
End DECIDE_PROD.

(** * Decision procedures for lists *)

Instance decide_In {A}:
  (forall (x y: A), Decision (x = y)) ->
  (forall (a: A) (l: list A), Decision (In a l)) :=
    @In_dec A.

Instance decide_Forall {A} (P: A -> Prop):
  (forall a, Decision (P a)) ->
  (forall l, Decision (Forall P l)).
Proof.
  intros HP l.
  induction l.
  * left.
    constructor.
  * destruct (decide (Forall P l)) as [Hl | Hl].
    destruct (decide (P a)) as [Ha | Ha].
    + left.
      constructor;
      assumption.
    + right.
      inversion 1.
      tauto.
    + right.
      inversion 1.
      tauto.
Defined.

Instance list_decide_eq {A} `{forall (x y: A), Decision (x = y)} :
  forall (xs ys: list A), Decision (xs = ys).
Proof. intros; apply list_eq_dec; auto. Qed.

(** * Decision procedures from [compare] *)

(** This takes care of many orders, which are defined as, say,
  [le x y := compare x y <> Gt]. *)

Instance comparison_eq_dec (x y: comparison): Decision (x = y).
Proof.
  red.
  decide equality.
Defined.

Program Instance comparison_ne_dec (x y: comparison): Decision (x <> y) :=
  match decide (x = y) with
    | left Hne => right _
    | right Hnne => left _
  end.

(** Decision and equivalence *)

Local Program Instance decide_rewrite P Q (Heq: P <-> Q) `(Decision P): Decision Q :=
  match decide P with
    | left _ => left _
    | right _ => right _
  end.
Obligation 1.
tauto.
Qed.

Obligation 2.
intros contra; elim wildcard'; tauto.
Qed.


(*
Local Instance decide_rewrite P Q (Heq: P <-> Q) `(Decision P): Decision Q :=
  match decide P with
    | left _ => left _
    | right _ => right _
  end.
Proof.
  abstract tauto.
  abstract tauto.
Defined.
 *)

(** Decision and discriminable cases *)

Theorem decide_discr {A}
        (Q1 Q2 P: A -> Prop)
        (discr: forall i, {Q1 i} + {Q2 i})
        (dec_1: Decision (forall i, Q1 i -> P i))
        (dec_2: Decision (forall i, Q2 i -> P i)):
  Decision (forall i, P i).
Proof.
  unfold Decision in *.
  firstorder.
Defined.

(** * Facts *)
Section DecFacts.
  Context {A: Type} {P: Prop} `{Decision P}.

  Fact decide_true_if (t f: A) :
    P -> (if decide P then t else f) = t.
  Proof. intros; now destruct (decide _). Qed.

  Fact decide_false_if (t f: A) :
    ~P -> (if decide P then t else f) = f.
  Proof. intros; now destruct (decide _). Qed.

  Fact decide_impl_true (Q: Prop) (t f: A) :
    (Q -> P) -> Q -> (if decide P then t else f) = t.
  Proof. intros * HQP HQ; apply HQP in HQ; apply decide_true_if; auto. Qed.

  Fact decide_iff (Q: Prop) `{Decision Q} (t f: A) :
    (Q <-> P) -> (if decide P then t else f) = (if decide Q then t else f).
  Proof.
    intros * HQP.
    destruct (decide Q) as [HQ | HQ]; rewrite HQP in HQ;
      [apply decide_true_if | apply decide_false_if]; auto.
  Qed.

  Fact decide_neg (t f: A) :
    (if decide P then t else f) = (if decide (~P) then f else t).
  Proof. now destruct (decide P), (decide (~P)). Qed.

(*
  Fact decide_neg (t f: A) :
    (if decide P then t else f) = (if decide (~P) then f else t).
  Proof. now destruct (decide P), (decide (~P)). Qed.
   *)
  
End DecFacts.

Section DecEq.
  Context {A B: Type}.
  Context `{forall (x y: A), Decision (x = y)}.

  Fact decide_refl (x: A) (t f: B) :
    (if decide (x = x) then t else f) = t.
  Proof. intros; apply decide_true_if; auto. Qed.

  Fact decide_sym (x y: A) (t f: B) :
    (if decide (x = y) then t else f) = (if decide (y = x) then t else f).
  Proof. now apply decide_iff. Qed.

End DecEq.
