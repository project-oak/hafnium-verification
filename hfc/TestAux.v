(*
 * Copyright 2020 Jieung Kim (jieungkim@google.com) 
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


(* This file is to defined macro values of Hafnium *) 

From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

(* for shift opeartors *)
From Coq Require Import
     Init.Nat.

From ExtLib Require Import
     RelDec
     Data.String
     Structures.Monad
     Structures.Traversable
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
Require Import Coqlib sflib.


(* From HafniumCore *)
Require Import Lang.
Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.


Require Import Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.
Require Import BitNat.

Local Open Scope N_scope.


Definition DebugHigh := Syscall "hd".

(* In this file, we will add auxiliary definitions for testings. 
1. INSERT_YIELD
2. Fake initializations for memory 
*)
Section INSERT_YIELD_DEFINITION.

  Fixpoint INSERT_YIELD (s: stmt): stmt :=
    match s with
    | Seq s0 s1 => Seq (INSERT_YIELD s0) (INSERT_YIELD s1)
    | If c s0 s1 => If c (INSERT_YIELD s0) (INSERT_YIELD s1)
    | While c s => While c (INSERT_YIELD s)
    | _ => Yield #; s
    end
  .

End INSERT_YIELD_DEFINITION.

Section PTR_INITIALIZATIONS.
  
  (* JIEUNG: two kinds of definitions *) 
  Definition big_mem_flat (paddr: N) (st_size: nat) (size: nat) : val :=
    Vptr (Some paddr) (repeat (Vnat 0) (st_size * size)).
  
  Definition big_tree (paddr: N) (size: nat) : val :=
    Vptr (Some paddr) (repeat (Vptr None []) size). 
  
End PTR_INITIALIZATIONS.


Section WF_CONDITIONS.

  (* JIEUNG: TODO - I will add well-formed conditions for memories in here *)
  
End WF_CONDITIONS.
