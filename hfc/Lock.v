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
     Data.List
     Data.Option
     Data.Monads.OptionMonad.


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



Set Implicit Arguments.



From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.
Require Import BitNat.

Local Open Scope N_scope.

Module LOCK.

  Definition ident := N.

  Inductive LockEvent: Type -> Type :=
  | TryLockE (id: ident): LockEvent (unit + val) (* inl: is already running, inr: not *)
  | UnlockE (id: ident) (v: val): LockEvent unit
  (* | InitE (v: val): LockEvent ident *)
  | NewE: LockEvent ident
  .

  Definition get_id (v: val): option ident :=
    match v with
    | Vnat n => Some n
    | _ => None
    end
  .

  Inductive case: Type :=
  (* | case_init *)
  | case_new
  | case_release
  | case_acquire
  | case_other
  .

  Definition case_analysis (func_name: string): case :=
    if rel_dec func_name "Lock.release"
    then case_release
    else
      if rel_dec func_name "Lock.acquire"
      then case_acquire
      else
        if rel_dec func_name "Lock.new"
        then case_new
        else case_other
  .

  Definition sem: CallExternalE ~> itree (CallExternalE +' LockEvent +' GlobalE +' Event) :=
    (fun _ '(CallExternal func_name args) =>
       match case_analysis func_name with
       | case_new =>
         triggerSyscall "d" "lock-new" [Vnull] ;;
         (* v <- (unwrapN (nth_error args 0)) ;; *)
         (* id <- trigger (InitE v) ;; *)
         id <- trigger (NewE) ;;
         Ret (Vnat id, [])
       | case_release =>
         id <- (unwrapN (nth_error args 0 >>= get_id)) ;;
            v <- (unwrapN (nth_error args 1)) ;;
            triggerSyscall "d" "lock-unlock <--- " [Vnat id ; v] ;;
            trigger (UnlockE id v) ;;
            trigger EYield ;;
            Ret (Vnodef, [])
       | case_acquire =>
         (* triggerSyscall "d" "lock-lock" [Vnull] ;; *)
         (* trigger EYield ;; *)
         (* id <- (unwrapN (nth_error args 0) >>= (unwrapN <*> get_id)) ;; *)
         id <- (unwrapN (nth_error args 0 >>= get_id)) ;;
         (* triggerSyscall "d" "lock-lock looking for: " [Vnat id] ;; *)
            (* (trigger (LockE id)) >>= unwrapN >>= fun v => Ret (v, []) *)

            v <- (ITree.iter (fun _ => trigger EYield ;; trigger (TryLockE id)) tt) ;;
            (* v <- (ITree.iter (fun _ => *)
            (*                     v <- trigger (TryLockE id) ;; *)
            (*                       match v: unit + val with *)
            (*                       | inl _ => trigger EYield ;; Ret (inl tt) *)
            (*                       | inr v => Ret (inr v) *)
            (*                       end) tt) ;; *)

            triggerSyscall "d" "lock-lock   ---> " [Vnat id ; v] ;;
            Ret (v, [])
            (* v <- trigger (TryLockE id) ;; *)
            (* match v with *)
            (* | inr v => Ret (v, []) *)
            (* | inl _ => Ret (Vnull, []) *)
            (* end *)


            (* v <- (ITree.iter (fun _ => *)
            (*                     trigger EYield ;; *)
            (*                     trigger (TryLockE id)) tt) ;; *)
            (* v <- ((trigger (TryLockE id)) >>= unwrapN) ;; *)
            (* Ret (v, []) *)
       | _ => triggerNB "Lock-no such function"
       end)
  .

  Definition owned_heap := (N * (alist ident val))%type.

  (* Definition extract_to_print (al: alist ident val): unit := tt. *)
  
  Definition debug_print (A: Type) (printer: A -> unit) (content: A): A :=
    let unused := printer content in content.
  Extract Constant debug_print =>
  (* "fun printer content -> printer content ; content" *)
  "fun printer content -> content"
  .
  Variable alist_printer: alist ident val -> unit.
  (* Variable dummy_client: unit -> unit. *)
  (* Extract Constant dummy_client => "fun x -> x". *)
  Extract Constant alist_printer =>
  "
  let rec nat_to_int = function | O -> 0 | S n -> succ (nat_to_int n) in
  fun al -> print_string ""<LOCKSTATE> "" ; print_int (nat_to_int (length al)) ; print_string "" "" ; (List.iter (fun kv -> print_int (nat_to_int (fst kv)) ; print_string "" "") al) ; print_endline "" "" "
  .

  (************* TODO: SEPARATE COAMLCOQ.ML ************************)
  (************* TODO: SEPARATE COAMLCOQ.ML ************************)
  (************* TODO: SEPARATE COAMLCOQ.ML ************************)
  (************* TODO: SEPARATE COAMLCOQ.ML ************************)
  (************* TODO: SEPARATE COAMLCOQ.ML ************************)
  (************* TODO: SEPARATE COAMLCOQ.ML ************************)

  Variable nat_printer: ident -> unit.
  Extract Constant nat_printer =>
  "
  let rec nat_to_int = function | O -> 0 | S n -> succ (nat_to_int n) in
  fun n -> print_int (nat_to_int n)
  "
  .

  Variable failwith: forall {T}, string -> T.
  Extract Constant failwith =>
  "
  let cl2s = fun cl -> String.concat """" (List.map (String.make 1) cl) in
  fun s -> failwith (cl2s s)
  "
  .



  (*
  Print Nat.RelDec_eq.
  Print Nat.eqb.
  Print N.eqb.
  Print Nat.RelDec_eq.
  Print Map_alist.
  Print Instances RelDec.
   *)

  
  (* JIEUNG: TODO : Do we have pre-defined instance for the following one? *)
  Global Instance RelDec_eq : RelDec (@eq N) :=
    { rel_dec := N.eqb }.
  
  
  Goal (Maps.lookup (Map:= Map_alist RelDec_eq N) 1 (Maps.add 1 10 Maps.empty)) = Some 10. ss. Qed.
  Goal (Maps.lookup (Map:= Map_alist RelDec_eq N) 2 (Maps.add 1 10 Maps.empty)) = None. ss. Qed.
  Goal (Maps.lookup (Map:= Map_alist RelDec_eq N) 1 (Maps.add 1 10 (Maps.empty (Map:=Map_alist _ _))))
  = Some 10. ss. Qed.
  Goal (Maps.lookup (Map:=Map_alist RelDec_eq N)
                    2 (Maps.add (Map:=Map_alist RelDec_eq N) 1 10
                                (Maps.empty
                (Map:=Map_alist RelDec_eq N)))) = Some 10. ss. Abort.

  (* Local Instance MyMap {V}: (Map nat V (alist nat V)) := Map_alist Nat.RelDec_eq V. *)
  (* Goal (Maps.lookup 2 (Maps.add 1 10 (Maps.empty (Map:=Map_alist _ _)))) = Some 10. ss. Abort. *)
  Local Instance MyMap: (Map nat val (alist nat val)) := Map_alist Nat.RelDec_eq val.

  Definition handler: LockEvent ~> stateT owned_heap (itree (GlobalE +' Event)) :=
    (* State.interp_state  *)
    fun _ e '(ctr, m) =>
      match e with
      | UnlockE k v =>
        (* let k := debug_print nat_printer k in *)
        let m := debug_print alist_printer m in
        let m' := debug_print alist_printer (Maps.add k v m) in
        match Maps.lookup k m with
        | Some _ => failwith "UNLOCKING TWICE"
        | None => Ret ((ctr, m'), tt)
        end
      | TryLockE k =>
        match Maps.lookup k m with
        | Some v =>
          let m := debug_print alist_printer m in
          let m' := debug_print alist_printer (Maps.remove k m) in
          Ret ((ctr, m'), inr v)
          (* Ret ((ctr, Maps.remove k m), inr v) *)
        | None => Ret ((ctr, m), inl tt)
        end
      (* | WHY_ANY_NAME_WORKS_HERE_THIS_IS_WEIRD => Ret ((S ctr, m), ctr) *)
      (* | InitE v => *)
      (*   let m := debug_print alist_printer m in *)
      (*   let m' := debug_print alist_printer (Maps.add ctr v m) in *)
      (*   Ret ((S ctr, m'), ctr) *)
      | NewE =>
        let m := debug_print alist_printer m in
        Ret ((ctr + 1, m), ctr)
      end
  .

  Definition modsem: ModSem :=
    mk_ModSem
      (fun s => existsb (string_dec s) ["Lock.release" ; "Lock.acquire" ; "Lock.new"])
      (* in_dec Strings.String.string_dec s ["Lock.unlock" ; "Lock.lock" ; "Lock.init"]) *)
      _
      (0, Maps.empty)
      LockEvent
      handler
      sem
  .

End LOCK.

