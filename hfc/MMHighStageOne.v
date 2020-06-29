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
From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

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
Require Import TestAux.
Require Import Lang.
Require Import Types.
Require Import MpoolConcur.
Require Import ArchMM.
Require Import Lock.

Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Module HighSpecDummyTest.

Require Import Any.

  Definition ident := nat.
  
  Instance RelDec_ident: RelDec (@eq ident) :=
    { rel_dec := fun n0 n1 => if (Nat.eqb n0 n1) then true else false}.
  
  Inductive PERM_TY :=
  | ABSENT | VALID.
  
  Inductive PTE_TY :=
  | BOOTED
  | PTE (level : nat) (addr : nat) (perm : PERM_TY).

  Record pt_entry: Type := mkPTE {value: PTE_TY}.
  
  Definition manager : Type := ident -> option pt_entry.
  
  Fixpoint pte_init_aux (vs : val): val :=
    match vs with
    | (Vabs a) =>
      match downcast a pt_entry with
      | Some (mkPTE value)  =>
        match value with 
        | BOOTED => Vabs (upcast (PTE 0 0 ABSENT))
        | PTE _ _ _ => Vabs (upcast (PTE 0 0 ABSENT))
        end
      | _ => Vnodef
      end
    | _ => Vnodef
    end.

  (* TODO: Make a function *)
  

  
End HighSpecDummyTest.

(*
Module MMHighStage1.

End MMHighStage1.
*)
