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


Section NOTATIONTEST.
  Local Close Scope itree_scope.
  Local Open Scope monad_scope.
  From ExtLib Require Import OptionMonad.
  Print Instances Monad.
  Print Instances PMonad.
  Variable oa: option nat.
  Fail Check (a <- oa ;; a).
  Local Existing Instance Monad_option | 100.
  Local Existing Instance Monad_option | 0.
  Notation "x ?? c1 !! c2" := (@pbind _ _ _ _ _ c1 (fun x => c2))
                                (at level 61, c1 at next level, right associativity).
  Fail Check ((a ?? oa !! a): option nat).
  Notation "x <- c1 ;; c2" := (@pbind _ (PMonad_Monad Monad_option) _ _ _ c1 (fun x => c2))
                                (at level 61, c1 at next level, right associativity).
  Check ((a <- oa ;; Some a): option nat).
End NOTATIONTEST.

Notation "x <- c1 ;; c2" := (@pbind _ (PMonad_Monad Monad_option) _ _ _ c1 (fun x => c2))
                              (at level 61, c1 at next level, right associativity).



Require Import Any.

  Definition ident := nat.
  
  Instance RelDec_ident: RelDec (@eq ident) :=
    { rel_dec := fun n0 n1 => if (Nat.eqb n0 n1) then true else false}.
  
  Inductive PERM_TY :=
  | ABSENT | VALID.
  
  Inductive PTE_TY :=
  | BOOTED
  | PTE (level : nat) (addr : nat) (perm : PERM_TY).

Module HighSpecDummyTest.

  
  Record pt_entry: Type := mkPTE {value: PTE_TY}.
  
  Definition manager : Type := ident -> option pt_entry.

  Require Import Coq.Arith.Peano_dec.
  Check dec_eq_nat.
  
  Definition pte_init_aux (vs : list val@{expr.u1}): (val@{expr.u2} * list val@{expr.u3}) :=
    let retv := match vs with
                | [(Vabs a) ; (Vnat dec)] =>
                  unwrap (pte_v <- downcast a pt_entry ;;
                          let pte_new_v := 
                              (match pte_v with
                               | mkPTE value =>
                                 match value with 
                                 | BOOTED => PTE O O ABSENT
                                 | PTE level addr perm =>
                                   match dec with
                                   | O => PTE level addr perm
                                   | _ => PTE O O ABSENT
                                   end
                                 end
                               end) in
                          Some (Vabs (upcast pte_new_v))
                         ) Vnodef
                | _ => Vnodef
                end
    in (retv, nil).


  Definition pte_init_aux2 (vs : list val@{expr.u1}): (val@{expr.u2} * list val@{expr.u3}) :=
    let retv := match vs with
                | [(Vabs a)] =>
                  unwrap (pte_v <- downcast a pt_entry ;;
                          (match pte_v with
                           | mkPTE value =>
                             match value with 
                             | BOOTED => Some (Vabs (upcast BOOTED))
                             | PTE level addr perm => Some (Vabs (upcast (PTE level addr perm)))
                             end
                           end) 
                         ) Vnodef
                | _ => Vnodef
                end
    in (retv, nil).
  
  (*
    case_sum = fun (A B C : Type) (f : A -> C) (g : B -> C) (x : A + B) => 
    match x with
    | inl a => f a
    | inr b => g b
    end
    : Case Fun sum
   *)

  
  (*
    Error:
    In environment
    d : var
    res : var
    r : var
    The term "pte_init_aux" has type "list val@{Set} -> val@{Vnull.u0} * list val@{pte_init_aux.u0}" while it is expected to have type
    "list val@{expr.u1} -> val@{expr.u2} * list val@{expr.u3}" (cannot unify "list val@{expr.u1}" and "list val@{Set}").
   *)
                                                    

  (*
    mapT@{d r} = 
    fun (T : Type -> Type) (Traversable0 : Traversable T) => let (mapT) := Traversable0 in mapT
    : forall T : Type -> Type,
    Traversable T -> forall F : Type -> Type, Applicative.Applicative F -> forall A B : Type, (A -> F B) -> T A -> F (T B)
    
   *)
  
  (* JIEUNG: let's make a debugging message for abs types *)
  (* JIEUNG: let's test the way to build heap *)
  (*
  Definition pte_init (d : var) res r : stmt := 
    r #= GetOwnedHeap #;
      res #= (CoqCode [CBV r ; CBV d] pte_init_aux) #;
      PutOwnedHeap r.
   *)

  Definition main res : stmt :=
    (Debug "[high-model] Calling" Vnull) #;
    res #= (CoqCode [CBV (Vabs (upcast (mkPTE (PTE 1 100 ABSENT)))) ; CBV (Vnat 1)] pte_init_aux) #;
    DebugHigh "[high-model] Calling" res #;
    res #= (CoqCode [CBV  (Vabs (upcast (mkPTE (PTE 1 100 ABSENT)))) ; CBV (Vnat 0)] pte_init_aux) #;
    DebugHigh "[high-model] Calling" res #;
    res #= (CoqCode [CBV (Vabs (upcast (mkPTE BOOTED))) ; CBV (Vnat 0)] pte_init_aux) #;
    DebugHigh "[high-model] Call End" res #;
    res #= (CoqCode [CBV (Vabs (upcast (mkPTE BOOTED)))] pte_init_aux2) #;
    DebugHigh "[high-model] Call End" res.
    (* Put "high level test end:" res. *)
  
  Definition mainF: function.
      mk_function_tac main ([]: list var) (["res"] : list var).
  Defined.
  
  Definition program: program :=
    [
      ("main", mainF)
    ].
  
  Definition modsems: list ModSem := [program_to_ModSem program]. 
  
  (*
    Definition isem: itree Event unit :=
      eval_multimodule_multicore
        modsems [ "main" ; "alloc1F" ; "alloc2F" ].
   *)
  
End HighSpecDummyTest.

(*
Module MMHighStage1.

End MMHighStage1.
*)
