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
     RelDec
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ExtLib Require Import
     Sets ListSet.

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
Require Import Lang Lock.
Import LangNotations.
Require Import Any.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.



Set Implicit Arguments.




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




(** Note: Lock is internalized **)
Module MPOOLSPEC.

  Definition ident := nat.

  Instance RelDec_ident: RelDec (@eq ident) :=
    { rel_dec := fun n0 n1 => if (Nat.eqb n0 n1) then true else false}.

  Record mpool: Type := mk {
    chunklist: list (nat * nat); (* paddr, limit *)
    fallback: option ident; (* mpoolid *)
  }
  .

  Definition manager: Type := ident -> option mpool.
  Definition inital_manager: manager := fun _ => None.
  Definition update (m: manager) (k0: ident) (v: option mpool): manager :=
    fun k1 => if rel_dec k0 k1 then v else m k1
  .



  Let init_aux (vs: list val): (val * list val) :=
    let retv := match vs with
                | [(Vabs a) ; (Vptr (Some p_id) _)] =>
                  match downcast a manager with
                  | Some mm0 => let mm1 := (update mm0 p_id (Some (mk nil None))) in
                                Vabs (upcast mm1)
                  | _ => Vnodef
                  end
                | _ => Vnodef
                end
    in
    (retv, nil)
  .

  Definition init (p: var) r: stmt :=
    r #= GetOwnedHeap #;
    PutOwnedHeap (CoqCode [CBV r ; CBV p] init_aux) #;
    Skip
  .



  Let init_with_fallback_aux (vs: list val): (val * list val) :=
    let retv := match vs with
                | [(Vabs a) ; (Vptr (Some p_id) _) ; (Vptr (Some fb_id) _)] =>
                  match downcast a manager with
                  | Some mm0 => let mm1 := (update mm0 p_id (Some (mk nil (Some fb_id)))) in
                                Vabs (upcast mm1)
                  | _ => Vnodef
                  end
                | _ => Vnodef
                end
    in
    (retv, nil)
  .

  Definition init_with_fallback (p fallback: var) r: stmt :=
    r #= GetOwnedHeap #;
    PutOwnedHeap (CoqCode [CBV r ; CBV p ; CBV fallback] init_with_fallback_aux) #;
    Skip
  .

  Let check_fallback (vs: list val): (val * list val) :=
    let retv := match vs with
                | [(Vabs a) ; (Vptr (Some p_id) _)]=>
                  unwrap (mm <- downcast a manager ;;
                          mp <- mm p_id ;;
                          Some (is_some (mp.(fallback)): val)
                         ) Vnodef
                | _ => Vnodef
                end
    in
    (retv, nil)
  .

  Let get_chunk_list (vs: list val): (val * list val) :=
    let retv := match vs with
                | [(Vabs a) ; (Vptr (Some p_id) _)]=>
                  unwrap (mm <- downcast a manager ;;
                          mp <- mm p_id ;;
                          Some (Vabs (upcast mp.(chunklist)))
                         ) Vnodef
                | _ => Vnodef
                end
    in
    (retv, nil)
  .

  Definition add_chunk (mp: mpool) (chunk: nat * nat): mpool :=
    mk (chunk :: mp.(chunklist)) mp.(fallback)
  .

  Let fini_aux (vs: list val): (val * list val) :=
    match vs with
    | [(Vabs a0) ; (Vptr (Some p_id) _) ; (Vabs a1)]=>
      unwrap (mm0 <- downcast a0 manager ;;
              cl <- downcast a1 (list (nat * nat)) ;;
              mp <- mm0 p_id ;;
              fb_id <- mp.(fallback) ;;
              fb <- mm0 fb_id ;;
              match cl with
              | hd :: tl =>
                let mm1 := (update mm0 fb_id (Some (add_chunk fb hd))) in
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
                  unwrap (mm0 <- downcast a manager ;;
                          mp <- mm0 p_id ;;
                          let mm1 := (update mm0 p_id None) in
                          Some (Vabs (upcast mm1))
                         ) Vnodef
                | _ => Vnodef
                end
    in
    (retv, nil)
  .

  (*** NOTE: Very interesting point. *)
(*     It is somewhat desirable to call "add_chunk" (instead of "inlining") in high level spec too, *)
(*     because it will prevent code duplication. *)
(*     However, "add_chunk"'s interface expects low-level, and we only have high-level data. *)
(*     1) Call "add_chunk". We need some form of "abstraction relation" && non-det *)
(*        in order to rebuild low-level data from high-level one. *)
(*     2) Inline it. *)
(*    ***)

  (*** TODO: We access mp.(fallback) without locking it. *)
(*     I think we are implicitly exploiting the fact that this data is const. *)
(*   ***)

  (*** TODO: It would be better if CoqCode can update variable outside. Maybe we can use CBV/CBR here too. *)
(*   ***)
  Definition fini (p: var)
             cl r: stmt :=
    r #= GetOwnedHeap #;
    #if !(CoqCode [CBV r ; CBV p] check_fallback)
     then Return Vnull
     else Skip #;
    cl #= (CoqCode [CBV r ; CBV p] get_chunk_list) #;
    #while (Vtrue)
    do (
      Yield #;
      r #= GetOwnedHeap #;
      #if (CoqCode [CBR r ; CBV p ; CBR cl] fini_aux)
       then Skip
       else Break #;
      PutOwnedHeap r #;
      Skip
    )#;
    PutOwnedHeap (CoqCode [CBV r ; CBV p] fini_aux2) #;
    Skip
  .

End MPOOLSPEC.












