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
Require Import Coqlib sflib Coq.Arith.Peano_dec.
  

(* From HafniumCore *)
Require Import TestAux.
Require Import Lang.
Require Import Types.
Require Import MpoolConcur.
Require Import ArchMM.
Require Import Lock.

Import LangNotations.


Require Import Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.
Require Import BitNat.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Local Open Scope N_scope.


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

Section AbsData.

  (* common definition *)

  Definition ident := N.

  Instance RelDec_ident: RelDec (@eq ident) :=
    { rel_dec := fun n0 n1 => if (N.eqb n0 n1) then true else false}.

  (* mpool *)

  Record mpool: Type :=
    mk {
        chunklist: list (nat * nat); (* paddr, limit *)
        fallback: option ident; (* mpoolid *)
      }
  .

  Definition mp_manager: Type := ident -> option mpool.
  Definition inital_mp_manager: mp_manager := fun _ => None.
  Definition mp_update (m: mp_manager) (k0: ident) (v: option mpool): mp_manager :=
    fun k1 => if rel_dec k0 k1 then v else m k1
  .

  (* page table *)

  Inductive PERM_TY := | ABSENT | VALID.
  Inductive OWN_TY := | OWNED | UNOWNED.
  Inductive SHARED_TY := | EXCLUSIVE | SHARED.

  Inductive PTE_TY :=
  | PTENONE
  | PTE (owner: option N) (paddr : N) (level : N) (vaddr: option N) (perm : PERM_TY).

  Record pt_entry: Type := mkPTE {value: list PTE_TY}.

  Definition pt_manager : Type := ident -> option pt_entry.
  Definition inital_pt_manager: mp_manager := fun _ => None.
  Definition pt_update (m: pt_manager) (k0: ident) (v: option pt_entry): pt_manager :=
    fun k1 => if rel_dec k0 k1 then v else m k1
  .

End AbsData.


Module HighSpecDummyTest.
  
  Fixpoint pte_init_iter (base_addr: N) (level : N) (esize : N) (length : nat): list PTE_TY :=
    match length with
    | O => nil
    | S O => (PTE None base_addr level None ABSENT)::nil
    | S n =>
      let prev := pte_init_iter base_addr level esize n in
      let len := List.length prev in 
      prev ++ (PTE None (base_addr + (esize * (N.of_nat len))) level None ABSENT)::nil
    end.

  (* initialization of the pte entry *)
  Definition pte_init (vs : list val@{expr.u1}): (val@{expr.u2} * list val@{expr.u3}) :=
    let retv := match vs with
                | [(Vnat base_addr) ; (Vnat level) ; (Vnat esize) ;(Vnat len)] =>
                  unwrap (let new_ptes := pte_init_iter base_addr level esize (N.to_nat len) in
                          Some (Vabs (upcast new_ptes))
                         ) Vnodef
                | _ => Vnodef
                end
    in (retv, nil).

  (*
  Definition pte_init_aux2 (vs : list val@{expr.u1}): (val@{expr.u2} * list val@{expr.u3}) :=
    let retv := match vs with
                | [(Vabs a)] =>
                  unwrap (ptes <- downcast a pt_entry ;;
                          let new_ptes := 
                              (match ptes with
                               | mkPTE ptes_v =>
                                 match dec with
                                 | O => ptes_v (* use as it is *)
                                 | _ => pte_init ptes_v 
                                 end
                               end) in
                          Some (Vabs (upcast new_ptes))
                         ) Vnodef
                | _ => Vnodef
                end
    in (retv, nil).
    *)
  


  (* JIEUNG: strategy: 
     MPOOL and PAGE TABLE might have different structures (Is it true?)
     This prevents us to provide the same abstarct representation. 
     So, we can duplicate them. 
     we can initialize two data structures 
     1. MPOOL 
     2. PTE  
     Each one has valid field, which is a logical flag. When we use some parts of memory for page tables, 
     we will mark that part in MPOOL and PTE together.
     If it is marked, we can check PTE to see the proper value for page tables. 
     Diabling them is quite simliar 
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
    res #= (CoqCode [CBV (Vnat 4000) ; CBV (Vnat 1) ; CBV (Vnat 4) ; CBV (Vnat 4)] pte_init) #;
    DebugHigh "[high-model] Calling" res #;
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
Module MPOOLMMHIGHTest.

  Let mpool_init_aux (vs: list val): (val * list val) :=
    let retv := match vs with
                | [(Vabs a) ; (Vptr (Some p_id) _)] =>
                  match downcast a mp_manager with
                  | Some mm0 => let mm1 := (mp_update mm0 p_id (Some (mk nil None))) in
                                Vabs (upcast mm1)
                  | _ => Vnodef
                  end
                | _ => Vnodef
                end
    in
    (retv, nil)
  .
  
  Definition mpool_init (p: var) r: stmt :=
    r #= GetOwnedHeap #;
      PutOwnedHeap (CoqCode [CBV r ; CBV p] mpool_init_aux) #;
      Skip
  .



  Let mp_init_with_fallback_aux (vs: list val): (val * list val) :=
    let retv := match vs with
                | [(Vabs a) ; (Vptr (Some p_id) _) ; (Vptr (Some fb_id) _)] =>
                  match downcast a mp_manager with
                  | Some mm0 => let mm1 := (mp_update mm0 p_id (Some (mk nil (Some fb_id)))) in
                                Vabs (upcast mm1)
                  | _ => Vnodef
                  end
                | _ => Vnodef
                end
    in
    (retv, nil)
  .
  
  Definition mpool_init_with_fallback (p fallback: var) r: stmt :=
    r #= GetOwnedHeap #;
      PutOwnedHeap (CoqCode [CBV r ; CBV p ; CBV fallback] mp_init_with_fallback_aux) #;
      Skip
  .
  
  Let mpool_check_fallback (vs: list val): (val * list val) :=
    let retv := match vs with
                | [(Vabs a) ; (Vptr (Some p_id) _)]=>
                  unwrap (mm <- downcast a mp_manager ;;
                          mp <- mm p_id ;;
                          Some (is_some (mp.(fallback)): val)
                         ) Vnodef
                | _ => Vnodef
                end
    in
    (retv, nil)
  .
  
  Let mpool_get_chunk_list (vs: list val): (val * list val) :=
    let retv := match vs with
                | [(Vabs a) ; (Vptr (Some p_id) _)]=>
                  unwrap (mm <- downcast a mp_manager ;;
                          mp <- mm p_id ;;
                          Some (Vabs (upcast mp.(chunklist)))
                         ) Vnodef
                | _ => Vnodef
                end
    in
    (retv, nil)
  .
  
  Definition mpool_add_chunk (mp: mpool) (chunk: nat * nat): mpool :=
    mk (chunk :: mp.(chunklist)) mp.(fallback)
  .

  Let mp_fini_aux (vs: list val): (val * list val) :=
    match vs with
    | [(Vabs a0) ; (Vptr (Some p_id) _) ; (Vabs a1)]=>
      unwrap (mm0 <- downcast a0 mp_manager ;;
              cl <- downcast a1 (list (nat * nat)) ;;
              mp <- mm0 p_id ;;
              fb_id <- mp.(fallback) ;;
              fb <- mm0 fb_id ;;
              match cl with
              | hd :: tl =>
                let mm1 := (mp_update mm0 fb_id (Some (mpool_add_chunk fb hd))) in
                Some (Vtrue, [(Vabs (upcast mm1)) ; (Vabs (upcast tl))])
              | _ => Some (Vfalse, [(Vabs a0) ; (Vabs a1)])
              (* | _ => (Vfalse, [(Vabs (upcast mm0)) ; (Vabs (upcast nil))]) *)
              end
             ) (Vnodef, nil)
    | _ => (Vnodef, nil)
    end
  .

  Let fini_aux2 (vs: list val): (val * list val) :=
    let retv := match vs with
                | [(Vabs a) ; (Vptr (Some p_id) _)]=>
                  unwrap (mm0 <- downcast a mp_manager ;;
                          mp <- mm0 p_id ;;
                          let mm1 := (mp_update mm0 p_id None) in
                          Some (Vabs (upcast mm1))
                         ) Vnodef
                | _ => Vnodef
                end
    in
    (retv, nil)
  .

End MPOOLMMHIGHTest.
*)
