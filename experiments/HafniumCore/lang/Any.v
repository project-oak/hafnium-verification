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

Set Implicit Arguments.

Definition Any := { ty: Type & ty }.
Hint Unfold Any.
(* Notation Any := { ty: Type & ty }. *)

Definition excluded_middle_informative_extract_true := excluded_middle_informative.
Extract Constant excluded_middle_informative_extract_true => "true".

Definition downcast (a: Any) (T: Type): option T.
  destruct a.
  destruct (excluded_middle_informative_extract_true (x = T)).
  - subst. apply Some. assumption.
  - apply None.
Defined.

Definition upcast {T} (a: T): Any := existT id _ a.

Lemma downcast_spec
      a T t
      (CAST: downcast a T = Some t)
  :
    <<TY: projT1 a = T>> /\ <<VAL: projT2 a ~= t>>
.
Proof.
  unfold downcast in *. des_ifs. ss.
  simpl_depind. eauto.
Qed.

Lemma downcast_intro
      a T t
      (TY: projT1 a = T)
      (VAL: projT2 a ~= t)
  :
    <<CAST: downcast a T = Some t>>
.
Proof.
  unfold downcast in *. des_ifs. ss.
  dependent destruction e. ss.
Qed.

Lemma upcast_downcast
      T (a: T)
  :
    downcast (upcast a) T = Some a
.
Proof.
  eapply downcast_intro; ss.
Qed.

Definition Any_dec (a0 a1: Any): {a0=a1} + {a0<>a1}.
  destruct a0, a1.
  simpl_depind.
  destruct (excluded_middle_informative (x = x0)).
  - clarify.
    destruct (excluded_middle_informative (p = p0)).
    + clarify. left. rewrite sigT_eta. ss.
    + right. ii. simpl_depind. clarify.
  - right. ii. simpl_depind.
Defined.
