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
Require Import Any.
Require Import Program.
Require Import sflib.

Set Implicit Arguments.

(* TODO: use Iso? *)
Class LeibEq (A B: Type) := { leibeq: A = B }.
Arguments LeibEq: clear implicits.
Definition cast_sigT (a: {ty: Type & ty}) (B: Type) `{LeibEq (projT1 a) B}: B.
  rewrite <- leibeq. destruct a. simpl. auto.
Defined.
Global Program Instance LeibEq_rev (A B: Type) `{LeibEq A B}: LeibEq B A.
Next Obligation. rewrite leibeq. eauto. Defined.
Definition cast (A B: Type) `{LeibEq A B} (a: A): B. rewrite <- leibeq. apply a. Defined.
Global Program Instance LeibEq_refl (A: Type): LeibEq A A.

Lemma cast_sigT_existT
      (x: { ty: Type & ty }) X
      (TY: LeibEq (projT1 x) X)
  :
    x = existT id _ (@cast_sigT x X TY)
.
Proof.
  destruct x. destruct TY. ss. clarify.
Qed.
Lemma cast_sigT_eq
      Y (x: {ty: Type & ty}) (y: Y)
      (JMEQ: projT2 x ~= y)
      (LEIBEQ: LeibEq (projT1 x) Y)
  :
    cast_sigT x = y
.
Proof.
  unfold cast_sigT. unfold eq_rect_r. ss. des_ifs. ss.
  unfold eq_rect. des_ifs.
Qed.

Lemma cast_sigT_proj
      Y (x: {ty: Type & ty}) (y: Y)
      (LEIBEQ: LeibEq (projT1 x) Y)
      (EQ: cast_sigT x = y)
  :
      <<JMEQ: projT2 x ~= y>>
.
Proof.
  unfold cast_sigT in *. ss. des_ifs. ss. unfold eq_rect. des_ifs.
Qed.
Lemma sigT_eta
      (a: { A: Type & A})
      (b: { B: Type & B})
      (EQTY: projT1 a = projT1 b)
      (EQVAL: projT2 a ~= projT2 b)
  :
    a = b
.
Proof.
  destruct a, b; ss. clarify. apply JMeq_eq in EQVAL. clarify.
Qed.

