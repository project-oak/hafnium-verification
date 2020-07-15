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
Require Import Lang Any.
Import LangNotations.



Require Import Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.
Require Import BitNat.

Local Open Scope N_scope.

Set Implicit Arguments.



Module LoadStore.

  Definition main x sum: stmt :=
    sum #= Vnat 0#;
    x #= Vptr None (repeat (Vnat 0) 3)#;
    Put "" x#;
    (x @ 0 #:= 10)#;
    Put "" x#;
    (x @ 1 #:= 20)#;
    Put "" x#;
    (x @ 2 #:= 30)#;
    Put "" x#;
    Put "" sum#;
    sum #= sum + (x #@ 0)#;
    Put "" sum#;
    sum #= sum + (x #@ 1)#;
    Put "" sum#;
    sum #= sum + (x #@ 2)#;
    Put "" sum#;
    Skip
  .

  Definition function: function. mk_function_tac main ([]: list var) ["x" ; "sum"]. Defined.

  Definition program: program := [("main", function)].

  (* Extraction "LangTest.ml" load_store_program. *)
  (* Check (eval_whole_program program). *)

End LoadStore.


Section TMP.
  Variable a: var.
  Variable b: val.
  Check (Var a).
  Check (Val b).
  Local Open Scope expr_scope.
  Local Open Scope stmt_scope.
  Check ((Var a) + (Val b)).
End TMP.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.


Module Rec.

  Definition f x y r: stmt :=
    (#if x
      then (y #= (x - 1) #;
              r #= (Call "f" [CBV y]) #;
              r #= r + x)
      else (r #= 0)
    )
      #;
      Return r
  .

  Definition f_function: function. mk_function_tac f ["x"] ["local0" ; "local1"]. Defined.

  Definition main x r: stmt :=
    x #= 10 #;
      r #= (Call "f" [CBV x]) #;
      Put "" r
  .

  Definition main_function: function.
    mk_function_tac main ([]:list var) ["local0" ; "local1"]. Defined.

  Definition program: program := [("main", main_function) ;
                                    ("f", f_function)].

End Rec.



Module MutRec.

  Definition f x y r: stmt :=
    (#if x
      then (y #= (x - 1) #;
              r #= (Call "g" [CBV y]) #;
              r #= r + x)
      else (r #= 0)
    )
      #;
      Return r
  .

  Definition g x y r: stmt :=
    (#if x
      then (y #= (x - 1) #;
              r #= (Call "f" [CBV y]) #;
              r #= r + x)
      else (r #= 0)
    )
      #;
      Return r
  .

  Definition f_function: function. mk_function_tac f ["x"] ["local0" ; "local1"]. Defined.
  Definition g_function: function. mk_function_tac g ["x"] ["local0" ; "local1"]. Defined.

  Definition program: program := [("main", Rec.main_function) ;
                                    ("f", f_function) ;
                                    ("g", g_function)].
End MutRec.



(* YJ: if we just use "r", not "unused", something weird will happen *)
(* TODO: address it better *)
Module Move.
  Definition f (x accu y unused: var): stmt :=
    (#if x
      then (y #= (x - 1) #;
              (* Put "before call" accu #; *)
              unused #= (Call "f" [CBV y ; CBR accu]) #;
              (* Put "after call" accu #; *)
              accu #= accu + x #;
                                Skip
           )
      else
        (accu #= 0)
    )
      #;
      Return 77777
  .

  Definition main x accu unused: stmt :=
    x #= 10 #;
      accu #= 1000 #;
      unused #= (Call "f" [CBV x ; CBR accu]) #;
      Put "" accu
  .

  Definition f_function: function. mk_function_tac f ["x" ; "accu"]
                                                   ["local0" ; "local1"]. Defined.
  Definition main_function: function.
    mk_function_tac main ([]:list var) ["local0" ; "local1" ; "local2"]. Defined.

  Definition program: program := [("main", main_function) ;
                                    ("f", f_function)].

End Move.





Module CoqCode.

  Definition coqcode: list val -> (val * list val) :=
    (fun v =>
       match v with
       | hd :: _ => if excluded_middle_informative (exists w, w * w = hd)
                    then (Vtrue, nil)
                    else (Vfalse, nil)
       | _ => (Vfalse, nil)
       end).

  (* Extract Constant excluded_middle_informative => "true". (* YJ: To avouid crash *) *)
  (* Extract Constant coqcode => "fun _ -> print_endline ""Is Prop true?"" ; *)
  (*                                     if (read_int() = 0) then coq_Vtrue else coq_Vfalse *)
  (*                                     ". *)
  Extract Constant coqcode => "fun _ -> (coq_Vtrue, [])".

  Definition main x: stmt :=
    x #= 25 #;
      (#if (CoqCode [CBV x] coqcode)
        then Put "" 555
        else Put "" 666)
  .

  Definition main_function: function.
    mk_function_tac main ([]: list var) ["local0"]. Defined.

  Definition program: program := [("main", main_function)].

End CoqCode.


Module CoqCodeCBR.

  Definition coqcode: list val -> (val * list val) :=
    (fun v =>
       match v with
       | hd :: nil => (Vfalse, [50: val])
       | _ => (Vfalse, nil)
       end).

  Definition main x: stmt :=
    x #= 0 #;
    (CoqCode [CBR x] coqcode) #;
    #assume (x == 50) #;
    Put "Test(CoqCodeCBR) passed" Vnull #;
    Skip
  .

  Definition main_function: function.
    mk_function_tac main ([]: list var) ["local0"]. Defined.

  Definition program: program := [("main", main_function)].

  Definition modsems: list ModSem :=
    List.map program_to_ModSem [program].

  Definition isem: itree Event unit := eval_multimodule modsems.

End CoqCodeCBR.

Module Control.

  Definition f ctrl ret iter: stmt :=
    iter #= 10 #;
    ret #= 0 #;
    (* Put "" ctrl #; *)
    (* Put "" iter #; *)
    (* Put "" ret #; *)
    (* Put "" 7777777 #; *)
    #while iter
     do (
          iter #= iter - 1#;
          (* 0 --> break *)
          (* 1 --> continue *)
          (* 2 --> return *)
          (* 3 --> normal *)
          #if ctrl == 0 then Break else Skip #;
          (* Put "" 1111 #; *)
          ret #= ret + 1 #;
          #if ctrl == 1 then Continue else Skip #;
          (* Put "" 2222 #; *)
          ret #= ret + 10 #;
          #if ctrl == 2 then (Return (ret + 100)) else Skip #;
          (* Put "" 3333 #; *)
          ret #= ret + 1000 #;

          Skip
          ) #;
     Return ret
  .

  Definition f_function: function. mk_function_tac f ["ctrl"] ["local0" ; "local1"]. Defined.

  Definition main r: stmt :=
    r #= (Call "f" [CBV 0]) #; #assume (r == 0) #;
    r #= (Call "f" [CBV 1]) #; #assume (r == 10) #;
    r #= (Call "f" [CBV 2]) #; #assume (r == 111) #;
    r #= (Call "f" [CBV 3]) #; #assume (r == 10110) #;
    Skip
  .

  Definition main_function: function. mk_function_tac main ([]: list var) ["local0"]. Defined.

  Definition program: program := [("main", main_function) ;
                                    ("f", f_function)].

End Control.




Module DoubleReturn.

  Definition f : stmt :=
    Return 0 #; Return 1
  .

  Definition f_function: function. mk_function_tac f ([]: list var) ([]: list var). Defined.

  Definition main r :=
    r #= (Call "f" []) #;
    #assume (r == 0) #;
    Skip
  .

  Definition main_function: function. mk_function_tac main ([]: list var) ["local0"]. Defined.

  Definition program: program := [("main", main_function) ;
                                    ("f", f_function)].

End DoubleReturn.




Module MultiCore.

  Definition main (n: N): stmt :=
    Put "" (n + 1) #;
    Put "" (n + 2) #;
    Yield #;
    Put "" (n + 3) #;
    Put "" (n + 4) #;
    Yield #;
    Put "" (n + 5) #;
    Put "" (n + 6) #;
    Skip
  .

  Definition main_function (n: N): function.
    mk_function_tac (main n) ([]: list var) ([]: list var). Defined.

  Definition program n: program := [("main", main_function n) ].

  Definition programs: list Lang.program := [program 0 ; program 10; program 20].

End MultiCore.





Module MultiCore2.

  Definition observer i: stmt :=
    i #= 20 #;
    #while i
    do (
      i #= i -1 #;
      #assume ("GVAR" % 2 == 0) #;
      Yield
    ) #;
    #if "GVAR" == 0 then AssumeFail else Skip #; (* Test if GlobalE actually worked *)
    Put "Test(MultiCore2) passed" Vnull
  .

  Definition adder i: stmt :=
    i #= 20 #;
    #while i
    do (
      i #= i - 1 #;
      "GVAR" #= "GVAR" + 1 #;
      "GVAR" #= "GVAR" + 1 #;
      Yield
    )
  .

  (* Definition main: stmt := *)
  (*   "GVAR" #:= 10 #; Yield *)
  (* . *)

  Definition observerF: function. mk_function_tac observer ([]: list var) (["i"]). Defined.
  Definition adderF: function. mk_function_tac adder ([]: list var) (["i"]). Defined.
  (* Definition mainF: function. mk_function_tac main ([]: list var) ([]: list var). Defined. *)

  Definition observerP: program := [("main", observerF) ].
  Definition adderP: program := [("main", adderF) ].
  (* Definition mainP: program := [("main", mainF) ]. *)

  (* Definition programs: list Lang.program := [ observerP ; adderP ; adderP ; mainP ]. *)
  Definition programs: list Lang.program := [ observerP ; adderP ; adderP ].

  Definition sem :=
   ITree.ignore
     (interp_GlobalE (round_robin (List.map eval_single_program programs)) []).

End MultiCore2.






Module MultiCoreMPSC.

  Definition producer i: stmt :=
    i #= 10 #;
    #while i
    do (
      Debug "PRODUCER: " i #;
      #if "GVAR" == 0
       then ("GVAR" #= i #; i #= i-1)
       else Skip #;
      Yield
    ) #;
    "SIGNAL" #= "SIGNAL" + 1
  .

  Definition consumer s: stmt :=
    s #= 0 #;
    #while true
    do (
      Debug "CONSUMER: " s #;
      #if "GVAR" == 0
       then Skip
       else s #= s + "GVAR" #;
            "GVAR" #= 0
      #;
      #if "SIGNAL" == 2 then Break else Skip #;
      Yield
    ) #;
    (* Put "" s #; *)
    #assume (s == 110) #;
    Put "Test(MultiCore3) passed" Vnull
  .

  Definition producerF: function. mk_function_tac producer ([]: list var) (["i"]). Defined.
  Definition consumerF: function. mk_function_tac consumer ([]: list var) (["s"]). Defined.

  Definition producerP: program := [("main", producerF) ].
  Definition consumerP: program := [("main", consumerF) ].

  Definition programs: list Lang.program := [ producerP ; consumerP ; producerP ].

  Definition sem :=
   ITree.ignore
     (interp_GlobalE (round_robin (List.map eval_single_program programs)) []).

End MultiCoreMPSC.



Module MultiModule.

  Definition f x y r: stmt :=
    (#if x
      then (y #= (x - 1) #;
              r #= (Call "g" [CBV y]) #;
              r #= r + x)
      else (r #= 0)
    )
    #;
    Return r
  .

  Definition g x y r: stmt :=
    (#if x
      then (y #= (x - 1) #;
              r #= (Call "f" [CBV y]) #;
              r #= r + x)
      else (r #= 0)
    )
    #;
    Return r
  .

  Definition f_function: function. mk_function_tac f ["x"] ["local0" ; "local1"]. Defined.
  Definition g_function: function. mk_function_tac g ["x"] ["local0" ; "local1"]. Defined.

  Definition main_program: program := [("main", Rec.main_function)].
  Definition f_program: program := [("f", f_function)].
  Definition g_program: program := [("g", g_function)].

  Definition modsems: list ModSem :=
    List.map program_to_ModSem [main_program ; f_program ; g_program].

  Definition isem: itree Event unit := eval_multimodule modsems.

End MultiModule.




Module MultiModuleGenv.

  Definition f: stmt :=
    "GVAR1" #= 1000 #;
    Return "GVAR2"
  .

  Definition g: stmt :=
    "GVAR2" #= 2000 #;
    Return "GVAR1"
  .

  Definition main: stmt :=
    (Call "f" []) #;
    #assume ((Call "g" []) == 1000) #;
    #assume ((Call "f" []) == 2000) #;
    Put "Test(MultiModuleGenv) passed" Vnull
  .

  Definition main_function: function.
    mk_function_tac main ([]:list var) ([]:list var). Defined.
  Definition f_function: function. mk_function_tac f ([]: list var) ([]: list var). Defined.
  Definition g_function: function. mk_function_tac g ([]: list var) ([]: list var). Defined.

  Definition main_program: program := [("main", main_function)].
  Definition f_program: program := [("f", f_function)].
  Definition g_program: program := [("g", g_function)].

  Definition modsems: list ModSem :=
    List.map program_to_ModSem [main_program ; f_program ; g_program].

  Definition isem: itree Event unit := eval_multimodule modsems.

End MultiModuleGenv.





Module MultiModuleLocalState.

  Inductive memoizeE: Type -> Type :=
  | GetM (k: N): memoizeE (option N)
  | SetM (k: N) (v: N): memoizeE unit
  .
  Definition f_sem: CallExternalE ~> itree (CallExternalE +' memoizeE +' GlobalE +' Event) :=
    (fun _ '(CallExternal func_name args) =>
       match args with
       | [Vnat k] =>
         v <- trigger (GetM k) ;;
           match v with
           | Some v => triggerSyscall "p" "HIT" [Vnull] ;; Ret (Vnat v, [])
           | None => triggerSyscall "p" "MISS" [Vnull] ;;
             match (k =? 0) with
             | true => Ret (Vnat 0, [])
             | _ => '(prev, _) <- trigger (CallExternal "g" [Vnat (N.pred k)]);;
                                match prev with
                                | Vnat prev =>
                                  let v := (prev + k)%N in
                                  trigger (SetM k v) ;; Ret (Vnat v, [])
                                | _ => triggerUB "memoizing_f"
                                end
             end
           end
       | _ => triggerUB "memoizing_f"
       end
    )
  .
  Definition f_owned_heap: Type := N -> option N.
  Definition update (oh: f_owned_heap) (k v: N): f_owned_heap :=
    fun x =>
      if N.eq_dec x k
      then Some v
      else oh x
  .
  Definition f_handler: memoizeE ~> stateT f_owned_heap (itree (GlobalE +' Event)) :=
    fun T e oh =>
      match e with
      | GetM k => Ret (oh, oh k)
      | SetM k v => Ret (update oh k v, tt)
      end
  .
  Definition f_ModSem: ModSem :=
    mk_ModSem
      (fun s => string_dec s "f")
      _
      (fun (_: N) => None: option N)
      memoizeE
      f_handler
      f_sem
  .

  Definition g x y r: stmt :=
    (#if x
      then (y #= (x - 1) #;
              r #= (Call "f" [CBV y]) #;
              r #= r + x)
      else (r #= 0)
    )
    #;
    Return r
  .
  Definition g_function: function. mk_function_tac g ["x"] ["local0" ; "local1"]. Defined.
  Definition g_program: program := [("g", g_function)].

  Definition main r: stmt :=
      r #= (Call "f" [CBV 10]) #;
      Put "" r #;

      Put "" 99999 #;
      Put "" 99999 #;
      Put "" 99999 #;

      r #= (Call "f" [CBV 10]) #;
      Put "" r #;

      Put "" 99999 #;
      Put "" 99999 #;
      Put "" 99999 #;

      r #= (Call "f" [CBV 5]) #;
      Put "" r #;

      Put "" 99999 #;
      Put "" 99999 #;
      Put "" 99999 #;

      r #= (Call "f" [CBV 8]) #;
      Put "" r #;

      Skip
  .
  Definition main_function: function.
    mk_function_tac main ([]: list var) ["local0"]. Defined.
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
  Definition f_sem: CallExternalE ~> itree (CallExternalE +' memoizeE +' GlobalE +' Event) :=
    (fun _ '(CallExternal func_name args) =>
       match args with
       | [Vnat v] => trigger EYield ;; trigger (SetM v) ;; Ret (Vnull, [])
       | _ => trigger EYield ;; v <-  trigger (GetM) ;; Ret (v, [])
       end)
  .

  Definition f_owned_heap: Type := val.

  Definition f_handler: memoizeE ~> stateT f_owned_heap (itree (GlobalE +' Event)) :=
    fun T e oh =>
      match e with
      | GetM => Ret (oh, oh)
      | SetM v => Ret (v, tt)
      end
  .
  Definition f_ModSem: ModSem :=
    mk_ModSem
      (fun s => string_dec s "f")
      _
      Vnull
      memoizeE
      f_handler
      f_sem
  .

  Definition g: stmt :=
    Return 10
  .
  Definition g_function: function. mk_function_tac g ([]: list var) ([]: list var). Defined.
  Definition g_program: program := [("g", g_function)].

  Definition main r: stmt :=
      (Call "f" [CBV 10]) #;
      (Call "g" []) #;
      Yield #; r #= (Call "f" []) #;
      #assume (r == 10) #;
      Debug "passed 1" Vnull #;
      (Call "g" []) #;
      Yield #; r #= (Call "f" []) #;
      #assume (r == 10) #;
      Debug "passed 2" Vnull #;
      Yield #; (Call "f" [CBV 20]) #;
      (Call "g" []) #;
      Yield #; r #= (Call "f" []) #;
      #assume (r == 20) #;
      Debug "passed 3" Vnull #;
      Put "Test(MultiModuleLocalStateSimple) passed" Vnull #;
      Skip
  .
  Definition main_function: function.
    mk_function_tac main ([]:list var) ["local0"]. Defined.
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



Module MultiModuleLocalStateSimpleLang.

  Module M1.
    Definition put v: stmt :=
      PutOwnedHeap v
    .
    Definition put_function: function. mk_function_tac put (["v"]: list var) ([]: list var). Defined.

    Definition get: stmt :=
      Return GetOwnedHeap
    .
    Definition get_function: function. mk_function_tac get ([]: list var) ([]: list var). Defined.

    Definition program: program := [("put", put_function) ; ("get", get_function)].
  End M1.

  Module M2.

    Inductive my_type: Type := RED | BLUE.

    Definition check_red: list val@{Type} -> (val * list val) :=
      (fun v =>
         match v with
         | Vabs a :: _ =>
           match downcast a my_type with
           | Some Red => (Vtrue, nil)
           | _ => (Vfalse, nil)
           end
         | _ => (Vfalse, nil)
         end).

    Definition main r: stmt :=
      (Call "put" [CBV 1]) #;
      r #= (Call "get" []) #;
      (* Put "r is: " r #; *)
      #assume (r == 1) #;
      (Call "put" [CBV (Vabs (upcast RED))]) #;
      (* Put "r is: " r #; *)
      r #= (Call "get" []) #;
      #assume (CoqCode [CBV r] check_red) #;
      Skip
    .
    Definition main_function: function. mk_function_tac main ([]: list var) (["r"]: list var). Defined.
    Definition program: program := [("main", main_function)].
  End M2.

  Definition modsems: list ModSem :=
    (List.map program_to_ModSem [M1.program ; M2.program])
  .

  Definition isem: itree Event unit := eval_multimodule modsems.

End MultiModuleLocalStateSimpleLang.



Module MultiModuleMultiCore.

  Definition producer i: stmt :=
    i #= 10 #;
    #while i
    do (
      Debug "PRODUCER: " i #;
      #if "GVAR" == 0
       then ("GVAR" #= i #; i #= i-1)
       else Skip #;
      Yield
    ) #;
    "SIGNAL" #= "SIGNAL" + 1
  .

  Definition consumer s: stmt :=
    s #= 0 #;
    #while true
    do (
      Debug "CONSUMER: " s #;
      #if "GVAR" == 0
       then Skip
       else s #= s + "GVAR" #;
            "GVAR" #= 0
      #;
      #if "SIGNAL" == 2 then Break else Skip #;
      Yield
    ) #;
    (* Put "" s #; *)
    #assume (s == 110) #;
    Put "Test(MultiCore3) passed" Vnull
  .

  Definition producerF: function. mk_function_tac producer ([]: list var) (["i"]). Defined.
  Definition consumerF: function. mk_function_tac consumer ([]: list var) (["s"]). Defined.

  Definition producerP: program := [("producer", producerF) ].
  Definition consumerP: program := [("consumer", consumerF) ].

  Definition programs: list Lang.program := [ producerP ; consumerP ].
  Definition modsems: list ModSem := List.map program_to_ModSem programs.

  Definition sem: itree Event unit :=
    eval_multimodule_multicore modsems [ "producer" ; "producer" ; "consumer" ].

End MultiModuleMultiCore.


Module MultiModuleMultiCoreLocalState.

  Inductive memoizeE: Type -> Type :=
  | GetM: memoizeE (val)
  | SetM (v: val): memoizeE unit
  .
  Definition f_sem: CallExternalE ~> itree (CallExternalE +' memoizeE +' GlobalE +' Event) :=
    (fun _ '(CallExternal func_name args) =>
       match args with
       | [Vnat v] => trigger EYield ;; trigger (SetM v) ;; Ret (Vnull, [])
       | _ => trigger EYield ;; v <-  trigger (GetM) ;; Ret (v, [])
       end)
  .

  Definition f_owned_heap: Type := val.

  Definition f_handler: memoizeE ~> stateT f_owned_heap (itree (GlobalE +' Event)) :=
    fun T e oh =>
      match e with
      | GetM => Ret (oh, oh)
      | SetM v => Ret (v, tt)
      end
  .
  Definition f_ModSem: ModSem :=
    mk_ModSem
      (fun s => string_dec s "f")
      _
      Vnull
      memoizeE
      f_handler
      f_sem
  .

  Definition setter: stmt :=
    (Call "f" [CBV 10]) #;
    "SIGNAL" #= 1 #;
    Skip
  .

  Definition getter: stmt :=
    #while "SIGNAL" == 0 do Yield #;
    #assume ((Call "f" []) == 10) #;
    Put "Test(MultiModuleMultiCoreLocalState) passed" Vnull #;
    Skip
  .

  Definition setterF: function.
    mk_function_tac setter ([]:list var) ([]:list var). Defined.
  Definition setterP: program := [("setter", setterF)].

  Definition getterF: function.
    mk_function_tac getter ([]:list var) ([]:list var). Defined.
  Definition getterP: program := [("getter", getterF)].

  Definition modsems: list ModSem :=
    (List.map program_to_ModSem [setterP ; getterP]) ++ [f_ModSem]
  .

  Definition isem: itree Event unit :=
    eval_multimodule_multicore modsems ["setter" ; "getter"].

End MultiModuleMultiCoreLocalState.


Module PrintAny.
 
  Inductive my_type: Type := RED | BLUE.
  Instance my_type_Showable: Showable my_type := { show := fun x => match x with | RED => "RED" | BLUE => "BLUE" end }.
 
    Definition main: stmt :=
      Put "Red is: " (Vabs (upcast RED)) #;
      Put "Blue is: " (Vabs (upcast BLUE)) #;
      Put "Test(PrintAny) passed" Vnull #;
      Skip
    .
    Definition main_function: function. mk_function_tac main ([]: list var) ([]: list var). Defined.
    Definition program: program := [("main", main_function)].
 
  Definition modsems: list ModSem :=
    (List.map program_to_ModSem [program])
  .
 
  Definition isem: itree Event unit := eval_multimodule modsems.
 
End PrintAny.


Module PrintTest.


Require Import BinaryString.

Include Raw.
Definition string_gen (n: N): string :=
  of_N n.

End PrintTest.
