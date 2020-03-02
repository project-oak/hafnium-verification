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
Require Import sflib.

Require Import ClassicalDescription.
About excluded_middle_informative.

(* From HafniumCore *)
Require Import Lang.
Import LangNotations.

Set Implicit Arguments.






Module LoadStore.

  Definition main x sum: stmt :=
    sum #:= Vnat 0#;
        x #:= Vptr None (repeat (Vnat 0) 3)#;
        #put x#;
        (Store x 0 10)#;
        #put x#;
        (Store x 1 20)#;
        #put x#;
        (Store x 2 30)#;
        #put x#;
        #put sum#;
        sum #:= sum + (Load x 0)#;
                                #put sum#;
                                sum #:= sum + (Load x 1)#;
                                                        #put sum#;
                                                        sum #:= sum + (Load x 2)#;
                                                                                #put sum#;
                                                                                Skip
  .

  Definition function: function := mk_function [] (main "x" "sum").

  Definition program: program := [("main", function)].

  (* Extraction "LangTest.ml" load_store_program. *)
  Check (eval_program program).

End LoadStore.


Section TMP.
  Variable a: var.
  Variable b: val.
  Check (Var a).
  Check (Lit b).
  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.
  Check ((Var a) + (Lit b)).
End TMP.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.


Module Rec.

  Definition f x y r: stmt :=
    (#if x
      then (y #:= (x - 1) #;
              r #:= (Call "f" [CBV y]) #;
              r #:= r + x)
      else (r #:= 0)
    )
      #;
      Return r
  .

  Definition f_function: function := mk_function ["x"] (f "x" "local0" "local1").

  Definition main x r: stmt :=
    x #:= 10 #;
      r #:= (Call "f" [CBV x]) #;
      #put r
  .

  Definition main_function: function := mk_function [] (main "local0" "local1").

  Definition program: program := [("main", main_function) ;
                                    ("f", f_function)].

End Rec.



Module MutRec.

  Definition f x y r: stmt :=
    (#if x
      then (y #:= (x - 1) #;
              r #:= (Call "g" [CBV y]) #;
              r #:= r + x)
      else (r #:= 0)
    )
      #;
      Return r
  .

  Definition g x y r: stmt :=
    (#if x
      then (y #:= (x - 1) #;
              r #:= (Call "f" [CBV y]) #;
              r #:= r + x)
      else (r #:= 0)
    )
      #;
      Return r
  .

  Definition f_function: function := mk_function ["x"] (f "x" "local0" "local1").
  Definition g_function: function := mk_function ["x"] (g "x" "local0" "local1").

  Definition program: program := [("main", Rec.main_function) ;
                                    ("f", f_function) ;
                                    ("g", g_function)].
End MutRec.



(* YJ: if we just use "r", not "unused", something weird will happen *)
(* TODO: address it better *)
Module Move.
  Definition f (x y accu unused: var): stmt :=
    (#if x
      then (y #:= (x - 1) #;
              (* Put "before call" accu #; *)
              unused #:= (Call "f" [CBV y ; CBR accu]) #;
              (* Put "after call" accu #; *)
              accu #:= accu + x #;
                                Skip
           )
      else
        (accu #:= 0)
    )
      #;
      Return 77777
  .

  Definition main x accu unused: stmt :=
    x #:= 10 #;
      accu #:= 1000 #;
      unused #:= (Call "f" [CBV x ; CBR accu]) #;
      #put accu
  .

  Definition f_function: function := mk_function ["x" ; "accu"]
                                                      (f "x" "local0" "accu" "local1").
  Definition main_function: function :=
    mk_function [] (main "local0" "local1" "local2").

  Definition program: program := [("main", main_function) ;
                                    ("f", f_function)].

End Move.





Module CoqCode.

  Definition coqcode: list val -> val :=
    (fun v =>
       match v with
       | hd :: _ => if excluded_middle_informative (exists w, w * w = hd)
                    then Vtrue
                    else Vfalse
       | _ => Vfalse
       end).

  (* Extract Constant excluded_middle_informative => "true". (* YJ: To avouid crash *) *)
  (* Extract Constant coqcode => "fun _ -> print_endline ""Is Prop true?"" ; *)
  (*                                     if (read_int() = 0) then coq_Vtrue else coq_Vfalse *)
  (*                                     ". *)
  Extract Constant coqcode => "fun _ -> coq_Vtrue".

  Definition main x: stmt :=
    x #:= 25 #;
      (#if (CoqCode [Var x] coqcode)
        then #put 555
        else #put 666)
  .

  Definition main_function: function :=
    mk_function [] (main "local0").

  Definition program: program := [("main", main_function)].

End CoqCode.



Module Control.

  Definition f ctrl ret iter: stmt :=
    iter #:= 10 #;
    ret #:= 0 #;
    (* #put ctrl #; *)
    (* #put iter #; *)
    (* #put ret #; *)
    (* #put 7777777 #; *)
    #while iter
     do (
          iter #:= iter - 1#;
          (* 0 --> break *)
          (* 1 --> continue *)
          (* 2 --> return *)
          (* 3 --> normal *)
          #if ctrl == 0 then Break else Skip #;
          (* #put 1111 #; *)
          ret #:= ret + 1 #;
          #if ctrl == 1 then Continue else Skip #;
          (* #put 2222 #; *)
          ret #:= ret + 10 #;
          #if ctrl == 2 then (Return (ret + 100)) else Skip #;
          (* #put 3333 #; *)
          ret #:= ret + 1000 #;

          Skip
          ) #;
     Return ret
  .

  Definition f_function: function := mk_function ["ctrl"] (f "ctrl" "local0" "local1").

  Definition main r: stmt :=
    r #:= (Call "f" [CBV 0]) #; #if r == 0 then Skip else Assume #;
    r #:= (Call "f" [CBV 1]) #; #if r == 10 then Skip else Assume #;
    r #:= (Call "f" [CBV 2]) #; #if r == 111 then Skip else Assume #;
    r #:= (Call "f" [CBV 3]) #; #if r == 10110 then Skip else Assume #;
    Skip
  .

  Definition main_function: function :=
    mk_function [] (main "local0")
  .

  Definition program: program := [("main", main_function) ;
                                    ("f", f_function)].

End Control.




Module DoubleReturn.

  Definition f : stmt :=
    Return 0 #; Return 1
  .

  Definition f_function: function := mk_function [] f.

  Definition main r :=
    r #:= (Call "f" []) #;
    #if ! (r == 0) then Assume else Skip #;
    Skip
  .

  Definition main_function: function :=
    mk_function [] (main "local0")
  .

  Definition program: program := [("main", main_function) ;
                                    ("f", f_function)].

End DoubleReturn.




Module MultiCore.

  Definition main (n: nat): stmt :=
    #put (n + 1) #;
    #put (n + 2) #;
    Yield #;
    #put (n + 3) #;
    #put (n + 4) #;
    Yield #;
    #put (n + 5) #;
    #put (n + 6) #;
    Skip
  .

  Definition main_function n: function :=
    mk_function [] (main n)
  .

  Definition program n: program := [("main", main_function n) ].

  Definition programs: list Lang.program := [program 0 ; program 10; program 20].

End MultiCore.




Module MultiModule.

  Definition f x y r: stmt :=
    (#if x
      then (y #:= (x - 1) #;
              r #:= (Call "g" [CBV y]) #;
              r #:= r + x)
      else (r #:= 0)
    )
    #;
    Return r
  .

  Definition g x y r: stmt :=
    (#if x
      then (y #:= (x - 1) #;
              r #:= (Call "f" [CBV y]) #;
              r #:= r + x)
      else (r #:= 0)
    )
    #;
    Return r
  .

  Definition f_function: function := mk_function ["x"] (f "x" "local0" "local1").
  Definition g_function: function := mk_function ["x"] (g "x" "local0" "local1").

  Definition main_program: program := [("main", Rec.main_function)].
  Definition f_program: program := [("f", f_function)].
  Definition g_program: program := [("g", g_function)].

  Definition modsems: list ModSem :=
    List.map program_to_ModSem [main_program ; f_program ; g_program].

  Definition isem: itree Event unit := eval_multimodule modsems.

End MultiModule.



Module MultiModuleLocalState.

  Inductive memoizeE: Type -> Type :=
  | GetM (k: nat): memoizeE (option nat)
  | SetM (k: nat) (v: nat): memoizeE unit
  .
  Definition f_sem: CallExternalE ~> itree (CallExternalE +' Event +' memoizeE) :=
    (fun _ '(CallExternal func_name args) =>
       match args with
       | [Vnat k] =>
         v <- trigger (GetM k) ;;
           match v with
           | Some v => triggerSyscall "p" "HIT" [Vnull] ;; Ret (Vnat v, [])
           | None => triggerSyscall "p" "MISS" [Vnull] ;;
             match k with
             | O => Ret (Vnat O, [])
             | _ => '(prev, _) <- trigger (CallExternal "g" [Vnat (Nat.pred k)]);;
                                match prev with
                                | Vnat prev =>
                                  let v := (prev + k)%nat in
                                  trigger (SetM k v) ;; Ret (Vnat v, [])
                                | _ => triggerUB "memoizing_f"
                                end
             end
           end
       | _ => triggerUB "memoizing_f"
       end
    )
  .
  Definition f_owned_heap: Type := nat -> option nat.
  Definition update (oh: f_owned_heap) (k v: nat): f_owned_heap :=
    fun x =>
      if Nat.eq_dec x k
      then Some v
      else oh x
  .
  Definition f_handler: memoizeE ~> stateT f_owned_heap (itree Event) :=
    fun T e oh =>
      match e with
      | GetM k => Ret (oh, oh k)
      | SetM k v => Ret (update oh k v, tt)
      end
  .
  Definition f_ModSem: ModSem :=
    mk_ModSem
      (fun s => string_dec s "f")
      (fun (_: nat) => None: option nat)
      memoizeE
      f_handler
      f_sem
  .

  Definition g x y r: stmt :=
    (#if x
      then (y #:= (x - 1) #;
              r #:= (Call "f" [CBV y]) #;
              r #:= r + x)
      else (r #:= 0)
    )
    #;
    Return r
  .
  Definition g_function: function := mk_function ["x"] (g "x" "local0" "local1").
  Definition g_program: program := [("g", g_function)].

  Definition main r: stmt :=
      r #:= (Call "f" [CBV 10]) #;
      #put r #;

      #put 99999 #;
      #put 99999 #;
      #put 99999 #;

      r #:= (Call "f" [CBV 10]) #;
      #put r #;

      #put 99999 #;
      #put 99999 #;
      #put 99999 #;

      r #:= (Call "f" [CBV 5]) #;
      #put r #;

      #put 99999 #;
      #put 99999 #;
      #put 99999 #;

      r #:= (Call "f" [CBV 8]) #;
      #put r #;

      Skip
  .
  Definition main_function: function := mk_function [] (main "local0").
  Definition main_program: program := [("main", main_function)].

  Definition modsems: list ModSem :=
    [f_ModSem] ++ List.map program_to_ModSem [main_program ; g_program].

  Definition isem: itree Event unit := eval_multimodule modsems.

End MultiModuleLocalState.




Module MultiModuleLocalStateSimple.

  Inductive memoizeE: Type -> Type :=
  | GetM: memoizeE (val)
  | SetM (v: val): memoizeE unit
  .
  Definition f_sem: CallExternalE ~> itree (CallExternalE +' Event +' memoizeE) :=
    (fun _ '(CallExternal func_name args) =>
       match args with
       | [Vnat v] => trigger EYield ;; trigger (SetM v) ;; Ret (Vnull, [])
       | _ => trigger EYield ;; v <-  trigger (GetM) ;; Ret (v, [])
       end)
  .

  Definition f_owned_heap: Type := val.

  Definition f_handler: memoizeE ~> stateT f_owned_heap (itree Event) :=
    fun T e oh =>
      match e with
      | GetM => Ret (oh, oh)
      | SetM v => Ret (v, tt)
      end
  .
  Definition f_ModSem: ModSem :=
    mk_ModSem
      (fun s => string_dec s "f")
      Vnull
      memoizeE
      f_handler
      f_sem
  .

  Definition g: stmt :=
    Return 10
  .
  Definition g_function: function := mk_function [] (g).
  Definition g_program: program := [("g", g_function)].

  Definition main r: stmt :=
      (Call "f" [CBV 10]) #;
      (Call "g" []) #;
      Yield #; r #:= (Call "f" []) #;
      #if r == 10 then Skip else Assume #;
      Debug "passed 1" Vnull #;
      (Call "g" []) #;
      Yield #; r #:= (Call "f" []) #;
      #if r == 10 then Skip else Assume #;
      Debug "passed 2" Vnull #;
      Yield #; (Call "f" [CBV 20]) #;
      (Call "g" []) #;
      Yield #; r #:= (Call "f" []) #;
      #if r == 20 then Skip else Assume #;
      Debug "passed 3" Vnull #;
      Put "Test(MultiModuleLocalStateSimple) passed" Vnull #;
      Skip
  .
  Definition main_function: function := mk_function [] (main "local0").
  Definition main_program: program := [("main", main_function)].

  Definition modsems1: list ModSem :=
    (List.map program_to_ModSem [main_program ; g_program]) ++ [f_ModSem]
  .
  Definition modsems2: list ModSem :=
    [f_ModSem] ++ (List.map program_to_ModSem [main_program ; g_program])
  .

  Definition isem1: itree Event unit := eval_multimodule modsems1.
  Definition isem2: itree Event unit := eval_multimodule modsems2.

End MultiModuleLocalStateSimple.




Section RUN.
Variable shuffle: forall A, list A -> list A.

(* Definition rr_match {E R} `{Event -< E} *)
(*            (rr : list (itree E R) -> itree E R) *)
(*            (q:list (itree E R)) : itree E R *)
(*   := *)
(*     match q with *)
(*     | [] => triggerUB *)
(*     | t::ts => *)
(*       match observe t with *)
(*       | RetF _ => Tau (rr ts) *)
(*       | TauF u => Tau (rr (u :: ts)) *)
(*       | @VisF _ _ _ X o k => Vis o (fun x => rr (shuffle (k x :: ts))) *)
(*       end *)
(*     end. *)

(* CoFixpoint round_robin {E R} `{Event -< e} (q:list (itree E R)) : itree E R := *)
(*   rr_match round_robin q. *)
Definition rr_match {R}
           (rr : list (itree Event R) -> itree Event unit)
           (q:list (itree Event R)) : itree Event unit
  :=
    match q with
    | [] => Ret tt
    | t::ts =>
      match observe t with
      | RetF _ => Tau (rr ts)
      | TauF u => Tau (rr (u :: ts))
      | @VisF _ _ _ X o k =>
        match o with
        | EYield => Vis o (fun x => rr (shuffle (k x :: ts)))
        | _ => Vis o (fun x => rr (k x :: ts))
        end
        (* match o with *)
        (* | Vis o (fun x => rr (shuffle (k x :: ts))) *)
        (* (match o in Event Y return X = Y -> itree Event unit with *)
        (* | EYield => fun pf => rr (k (eq_rect_r (fun T => T) tt pf) :: ts) *)
        (* | _ => fun _ => Vis o (fun x => rr (k x :: ts)) *)
        (* end) eq_refl *)
      end
    end.

CoFixpoint round_robin {R} (q:list (itree Event R)) : itree Event unit :=
  rr_match round_robin q.




Variable handle_Event: forall E R X, Event X -> (X -> itree E R) -> itree E R.
(* Extract Constant handle_Event => "handle_Event". *)

Definition run_till_yield_aux {R} (rr : itree Event R -> (itree Event R))
           (q: itree Event R) : (itree Event R)
  :=
    match observe q with
    | RetF _ => q
    | TauF u => Tau (rr u)
      (* w <- (rr u) ;; (Tau w) *)
    | @VisF _ _ _ X o k =>
      (match o in Event Y return X = Y -> itree Event R with
       | EYield => fun pf => k (eq_rect_r (fun T => T) tt pf)
       | _ => (* fun _ => Vis o (fun x => rr (k x)) *)
         fun _ => Tau (rr (handle_Event o k))
       end) eq_refl
      (* match o with *)
      (* | EYield => Vis o (fun x => rr (k x)) *)
      (* | _ => Vis o (fun x => rr (k x)) *)
      (* end *)
    (* Vis o (fun x => rr (shuffle (ts ++ [k x]))) *)
    end.

CoFixpoint run_till_yield {R} (q: itree Event R): (itree Event R) :=
  run_till_yield_aux run_till_yield q
.

Definition is_ret {E R} (q: itree E R): bool := match observe q with RetF _ => true | _ => false end.

Definition my_rr_match {R} (rr : list (itree Event R) -> list (itree Event R))
           (q:list (itree Event R)) : list (itree Event R)
  :=
    match q with
    | [] => []
    | t::ts =>
      let t2 := run_till_yield t in
      rr (shuffle (List.filter (negb <*> is_ret) (t2::ts)))
    end.

Fail CoFixpoint my_round_robin {R} (q:list (itree Event R)) : list (itree Event R) :=
  my_rr_match my_round_robin q.

End RUN.
