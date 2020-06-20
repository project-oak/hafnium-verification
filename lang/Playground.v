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
From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Structures.Foldable
     Structures.Reducible
     Structures.Maps
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

From ITree Require Import
     ITree ITreeFacts.

Import ITreeNotations.
Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Require Import Any.
Require Import sflib.

Require Import ClassicalDescription EquivDec.
About excluded_middle_informative.

Set Implicit Arguments.


(* YJ: use RelDec? *)
Instance PFun_Map (K V: Type) (dec: forall k0 k1, {k0=k1} + {k0<>k1}):
                                                    (Map K V (K -> option V)) :=
  Build_Map
    (fun _ => None)
    (fun k0 v m => fun k1 => if dec k0 k1 then Some v else m k1)
    (fun k0 m => fun k1 => if dec k0 k1 then None else m k1)
    (fun k m => m k)
    (fun m0 m1 => fun k => match (m0 k) with
                           | Some v => Some v
                           | _ => m1 k
                           end)
.


Section TMP.
  Print Instances Case.
  Variable a: nat -> nat.
  Variable b: unit -> nat.
  Check ((@case_ _ _ _ case_sum) _ _ _ a b): (nat + unit) -> nat.
  Check ((@case_ _ _ _ case_sum) _ _ _ a b).
  Fail Check (case_ a b): Fun (nat + unit) nat.
  Fail Check (case_ a b).
  Check (@case_ _ Fun sum case_sum _ _ _ a b).
  Check (case_ (Case:=case_sum) a b).
End TMP.


Section INJECT.
  Context {A B E: Type -> Type}.
  Section TMP.
    Variable e: (A +' B) unit.
    Check ((inl1 e): ((A +' B) +' E) unit).
    (* Check (inl1 (inr1 e): (A +' B +' E) unit). *)
    Variable ee: (A +' B +' E) unit.
    Fail Check (ee: ((A +' B) +' E) unit).
  End TMP.

  Definition inject R (i: itree (A +' E) R) (before after: B R): itree (A +' B +' E) R :=
    interp (fun _ e =>
              match e with
              (* | inl1 a => trigger (inl1 (inl1 e)) *)
              (* | inr1 e => trigger (inr1 e) *)
              (* | inl1 a => ITree.spin (* trigger (inl1 e) *) *)
              (* | inr1 e => ITree.spin (* trigger (inr1 (inr1 e)) *) *)
              | inl1 a => trigger (inl1 a)
              | inr1 e => trigger (inr1 (inr1 e))
              end) i
  .

  (* B R 가지고 된다고 쳐도... R 을 받아서 itree가 뭔가를 해야 할텐데 (GetAny)
그것까지 inject 할 수는 없음...
   *)

End INJECT.

Section TMP.
  Variable (A B: Type -> Type).
  Variable R: Type.
  Context `{A -< B}.
  Context `{forall T, Embeddable (A T) (B T)}.
  Variable e: itree A R.
  Goal itree B R.
    clear H.
    eapply translate; try apply e; eauto.
  Qed.
  Goal itree B R.
    clear H0.
    eapply translate; try apply e; eauto.
  Qed.
End TMP.

Goal forall E R, (burn 200 (@ITree.spin E R)) = (burn 2 (ITree.spin)).
  reflexivity.
Qed.
