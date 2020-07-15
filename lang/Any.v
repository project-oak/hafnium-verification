(*
 * Copyright 2020 Youngju Song
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
Require Import sflib.
Require Import Program.
Require Import ClassicalDescription EquivDec.
Require Import String.
Generalizable Variables A T.
 


Set Implicit Arguments.

Definition excluded_middle_informative_extract_true := excluded_middle_informative.
Extract Constant excluded_middle_informative_extract_true => "true".


Class Showable (A: Type) := {
  show: A -> string;
}
.

Polymorphic Inductive Any: Type :=
  (* Any_intro : forall {A:Type} {x:A}, Any. *)
  Any_intro : forall `{Showable A} {x:A}, Any.
 


(* Arguments Any [A P]. *)

Polymorphic Definition downcast (a: Any) (T: Type): option T.
destruct a.
destruct (excluded_middle_informative_extract_true (A = T)).
- subst. apply Some. assumption.
- apply None.
Defined.

(* Polymorphic Definition upcast {T} (a: T): Any := @Any_intro _ a. *)
Polymorphic Definition upcast `{Showable T} (a: T): Any := @Any_intro _ _ a.

Arguments Any_intro {A} {H} x.

Instance unit_Showable: Showable unit := { show := fun _ => "()" }.
Program Instance Any_Showable: Showable Any.
Next Obligation.
  destruct X.
  exact (show x).
Defined.
Instance default_Showable {A}: Showable A | 50000 := { show := fun _ => "" }.
 
(* Arguments Any_intro {A} x. *)
Definition string_of_Any: Any -> string := show.
 



(* Lemma downcast_spec *)
(*       a T t *)
(*       (CAST: downcast a T = Some t) *)
(*   : *)
(*     <<TY: projT1 a = T>> /\ <<VAL: projT2 a ~= t>> *)
(* . *)
(* Proof. *)
(*   unfold downcast in *. des_ifs. ss. *)
(*   simpl_depind. eauto. *)
(* Qed. *)

(* Lemma downcast_intro *)
(*       a T t *)
(*       (TY: projT1 a = T) *)
(*       (VAL: projT2 a ~= t) *)
(*   : *)
(*     <<CAST: downcast a T = Some t>> *)
(* . *)
(* Proof. *)
(*   unfold downcast in *. des_ifs. ss. *)
(*   dependent destruction e. ss. *)
(* Qed. *)

(* Lemma upcast_downcast *)
(*       T (a: T) *)
(*   : *)
(*     downcast (upcast a) T = Some a *)
(* . *)
(* Proof. *)
(*   eapply downcast_intro; ss. *)
(* Qed. *)

Definition Any_dec (a0 a1: Any): {a0=a1} + {a0<>a1}.
  destruct a0, a1.
  simpl_depind.
  destruct (excluded_middle_informative_extract_true (A = A0)).
  - clarify.
    destruct (excluded_middle_informative_extract_true (H = H0)).
    + destruct (excluded_middle_informative_extract_true (x = x0)).
      * clarify. left. ss.
      * right. ii. simpl_depind. clarify.
    + right. ii. simpl_depind. clarify.
  - right. ii. simpl_depind.
Defined.



Module PLAYGROUND0.

  Set Printing Universes.
  Unset Universe Polymorphism.


(*** Coq.Init.Specif (not polymorphic) ***)
(* Inductive sigT (A : Type@{sigT.u0}) (P : A -> Type@{sigT.u1}) : Type@{max(sigT.u0,sigT.u1)} := *)
(*     existT : forall x : A, P x -> {x : A & P x} *)
(* {sigT.u1 sigT.u0} |=  *)


(*** Polymorphic ***)
(* sigT@{HafniumCore.Any.85 HafniumCore.Any.86} (A : Type@{HafniumCore.Any.85}) *)
(* (P : A -> Type@{HafniumCore.Any.86}) : Type@{max(HafniumCore.Any.85,HafniumCore.Any.86)} := *)
(*     existT : forall x : A, P x -> sigT@{HafniumCore.Any.85 HafniumCore.Any.86} P *)
(* HafniumCore.Any.85 HafniumCore.Any.86 |=  *)

  Definition Any := { ty: Type & ty }.
  (* Any = {ty : Type@{Any.u0} & ty} *)
  (*    : Type@{Any.u0+1} *)

  (* Any@{HafniumCore.Any.84} =  *)
  (* {ty : Type@{HafniumCore.Any.84} & ty} *)
  (*   : Type@{HafniumCore.Any.84+1} *)

  (* Definition downcast (a: Any) (T: Type): option T. *)
  Polymorphic Definition downcast (a: Any) (T: Type): option T.
  destruct a.
  destruct (excluded_middle_informative_extract_true (x = T)).
  - subst. apply Some. assumption.
  - apply None.
  Defined.

  Inductive val: Type := Vabs (a: Any).
  Variable a: Any.
  Check (@downcast a val).
  Variable v: val.
  Check (match v with
         | Vabs a => (@downcast a val)
         end).

  Inductive ModSem: Type := mk_ModSem {
    owned_heap: Type;
    initial_owned_heap: owned_heap;
  }
  .

  Polymorphic Fixpoint INITIAL (mss: list ModSem): list Any :=
    match mss with
    | [] => []
    | hd :: tl => (existT id _ hd.(initial_owned_heap)) :: INITIAL tl
    end
  .

  Polymorphic Definition upcast {T} (a: T): Any := @existT _ id _ a.
  Polymorphic Definition program_to_ModSem: ModSem := @mk_ModSem Any (upcast tt).

End PLAYGROUND0.

Module PLAYGROUND1.
  Section ANY.

  (* Polymorphic Universe i. *)
  (* Variable T : Type@{i}. *)

  Set Printing Universes.
  Unset Universe Polymorphism.

  Polymorphic Inductive Any: Type :=
    Any_intro : forall {A:Type} {x:A}, Any.

  (* Arguments Any [A P]. *)

  Polymorphic Definition downcast (a: Any) (T: Type): option T.
  destruct a.
  destruct (excluded_middle_informative_extract_true (A = T)).
  - subst. apply Some. assumption.
  - apply None.
  Defined.

  Polymorphic Definition upcast {T} (a: T): Any := @Any_intro _ a.

  End ANY.
  Arguments Any_intro {A} x.

  Polymorphic Inductive val: Type := Vabs (a: Any).
  Variable a: Any.
  Check (@downcast a val).
  Variable v: val.
  Check (Vabs (upcast (Vabs (upcast 0)))).
  Check (Vabs (upcast (Vabs (upcast (Vabs (upcast 0)))))).
  Check (match v with
         | Vabs a => (@downcast a val)
         end).

  Inductive ModSem: Type := mk_ModSem {
    owned_heap: Type;
    initial_owned_heap: owned_heap;
  }
  .

  Fixpoint INITIAL (mss: list ModSem): list Any :=
    match mss with
    | [] => []
    | hd :: tl => (Any_intro hd.(initial_owned_heap)) :: INITIAL tl
    end
  .

  Definition program_to_ModSem: ModSem := @mk_ModSem Any (upcast tt).

End PLAYGROUND1.

