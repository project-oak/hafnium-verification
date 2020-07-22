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

open Monad
open OptionMonad
open Any
open Lang

open MpoolSeq
open MpoolConcur
open CPUSeq
open MMStageOne
open MMHighStageOne
open LangTest

open List
open String



(* open CategoryKleisli *)
open CategoryOps
open Datatypes
open FMapAList
open Function
open ITreeDefinition
open Interp
open List0
open List1
open MapDefault
open Maps
open Monad
open Nat
open Recursion
open RelDec
open String0
open Subevent
open Sum
open Traversable
open BinaryString
open Sflib

module Nat = struct
  include Nat
  let rec to_int = function | O -> 0 | S n -> succ (to_int n)
  let rec of_int n = assert(n >= 0); if(n == 0) then O else S (of_int (pred n))
end

(* let shuffle: 'a list -> 'a list = fun xs ->
 *   let xis = List.map (fun x -> (Random.bits (), x)) xs in
 *   let yis = List.sort (fun x0 x1 -> Stdlib.compare (fst x0) (fst x1)) xis in
 *   List.map snd yis *)

let cl2s = fun cl -> String.concat "" (List.map (String.make 1) cl)

(*
let rec string_of_val v =
  match v with
  | Vnat n -> (string_of_int (Nat.to_int n)) ^ " "
  | Vptr(paddr, cts) ->
     let paddr = "(" ^ (match paddr with
                        | Some paddr -> string_of_int (Nat.to_int paddr)
                        | None -> "N") ^ ")"
     in
     if length cts == Nat.of_int 0
     then paddr ^ ". "
     else paddr ^ "[" ^
            (List.fold_left (fun s i -> s ^ " " ^ string_of_val i) "" cts) ^ "]"
  | Vabs(a) -> " some abstract value"
*)

let string_of_val v = cl2s (show_val v)

let print_val = fun v -> print_endline (string_of_val v)

let string_of_vals vs = List.fold_left (fun s i -> s ^ " " ^ string_of_val i) "" vs


(* JIEUNG: The following things are for mpool. Is there any way that we can provide 
 * those definitions with more user-friendly way than now? *)
let string_of_lock l =
  match l with
  | Vnat id -> (cl2s (BinaryString.of_N id))
  | _ -> failwith "Mpool not well-formed0"

let entry_size = 4

let rec string_of_chunk_list cl =
  match cl with
  | Vptr(Some(v), []) -> ""
  | Vptr(Some paddr, next :: (Vnat limit) :: others) ->
      (*
     (if (entry_size * (Nat.to_int limit)) != Nat.to_int (length (next :: (Vnat limit) :: others))
      then failwith "Mpool not well-formed4"
      else ()) ; *)
     "[" ^ (cl2s (BinaryString.of_N paddr)) ^ "~" ^  "(" ^ (cl2s (BinaryString.of_N paddr)) ^
     " + " ^ (string_of_int entry_size) ^ " * " ^ (cl2s (BinaryString.of_N limit)) ^ ") " ^
       string_of_chunk_list next
  | _ -> failwith "Mpool not well-formed1"

let string_of_mpool p =
  let rec foo padding p =
    match p with
    (*
    | Vptr(Some(O), []) -> "" *)
    (* | Vptr(_, [ lock ; chunk_list ; fallback ] ) -> *)
    | Vptr(_, lock :: chunk_list :: fallback :: _ ) ->
       string_of_lock lock ^ " --> " ^ string_of_chunk_list chunk_list ^ "\n"
       (* ^ padding ^ (foo (padding ^ "  ") fallback) *)
    | _ -> failwith "Mpool not well-formed2"
  in
  (foo "  " p)



(*
let string_of_lock l =
  match l with
  | Vnat id -> string_of_int (Nat.to_int id)
  | _ -> failwith "Mpool not well-formed0"

let entry_size = 4

let rec string_of_chunk_list cl =
  match cl with
  | Vptr(Some(O), []) -> ""
  | Vptr(Some paddr, next :: (Vnat limit) :: others) ->
     (if (entry_size * (Nat.to_int limit)) != Nat.to_int (length (next :: (Vnat limit) :: others))
      then failwith "Mpool not well-formed4"
      else ()) ;
     "[" ^ string_of_int (Nat.to_int paddr) ^ "~" ^ string_of_int ((Nat.to_int paddr) + entry_size * (Nat.to_int limit)) ^ ") " ^
       string_of_chunk_list next
  | _ -> failwith "Mpool not well-formed1"

let string_of_mpool p =
  let rec foo padding p =
    match p with
    | Vptr(Some(O), []) -> ""
    (* | Vptr(_, [ lock ; chunk_list ; fallback ] ) -> *)
    | Vptr(_, lock :: chunk_list :: fallback :: _ ) ->
       string_of_lock lock ^ " --> " ^ string_of_chunk_list chunk_list ^ "\n"
       (* ^ padding ^ (foo (padding ^ "  ") fallback) *)
    | _ -> failwith "Mpool not well-formed2"
  in
  (foo "  " p)

let rec make_hstruct_string ptes =
  match ptes with
  | [] -> ""
  | PTE (owner, addr, level, vaddr, perm)::tl ->
    match perm with
    | ABSENT -> "PTE: " ^ string_of_int (Nat.to_int level) ^ " " ^ string_of_int (Nat.to_int addr) ^ " ABSENT ; ;" 
        ^ make_hstruct_string tl
    | VALID -> "PTE: " ^ string_of_int (Nat.to_int level) ^ " " ^ string_of_int (Nat.to_int addr) ^ " VALID ; ;"
        ^ make_hstruct_string tl

let string_of_hstruct v =
  match v with
  | Vabs a ->
    let x = 
       pbind (coq_PMonad_Monad (Obj.magic coq_Monad_option))
       (Obj.magic (fun _ -> true)) (downcast a) (fun ptes -> Some (make_hstruct_string ptes)) 
    in
    (match x with
    | Some y -> y
    | None -> failwith "H struct not well-formed0")
  | _ -> failwith "H struct not well-formed2"
*)

(* let print_val =
 *   let rec go v =
 *     match v with
 *     | Vnat n -> print_string ((string_of_int (Nat.to_int n)) ^ " ")
 *     | Vptr(paddr, cts) ->
 *        (\* (print_string "[" ; List.iter go cts ; print_string "]") *\)
 *        let paddr = "(" ^ (match paddr with
 *                           | Some paddr -> string_of_int (Nat.to_int paddr)
 *                           | None -> "N") ^ ")"
 *        in
 *        if length cts == Nat.of_int 0
 *        then (print_string (paddr ^ ". "))
 *        else (print_string (paddr ^ "[") ; List.iter go cts ; print_string "] ")
 *   in
 *   fun v -> go v ; print_endline " " *)



(* JIEUNG: this is for adding messages using Syscall, NB, and UB *)
let handle_Event = fun e k ->
  match e with
  | ENB msg -> failwith ("NB:" ^ (cl2s msg))
  | EUB msg -> failwith ("UB:" ^ (cl2s msg))
  | ESyscall ('p'::[], msg, v::[]) ->
     print_string (cl2s msg) ; print_val v ; k (Obj.magic ())
  | ESyscall ('d'::[], msg, vs) ->
     (* print_string "<DEBUG> " ; print_string (cl2s msg) ;
      * * print_endline (string_of_vals vs) ; *)
      k (Obj.magic ())
  | ESyscall ('h'::'d'::[], msg, v::[]) ->
     print_endline (cl2s msg) ;
     (* print_endline (string_of_hstruct v) ; *)
     k (Obj.magic()) 
     (*
  | ESyscall ('d'::'b'::'u'::'g'::[], msg, _) ->
     print_endline (cl2s msg) ;
     print_endline "" ;
     k (Obj.magic ()) *)
  | ESyscall ('m'::'d'::[], msg, p::[]) ->
     print_endline (cl2s msg) ;
     print_endline (string_of_mpool p) ; 
     print_endline "" ;
     k (Obj.magic ()) 
  (*
  | ESyscall ('g'::[], _,   []) ->
     let x = read_int() in k (Obj.magic (Vnat (Nat.of_int x))) *)
  | ESyscall (cl,      msg, vs) ->
     print_string (cl2s msg) ; print_endline (cl2s cl) ;
     failwith "UNSUPPORTED SYSCALL"
  | EYield ->
     print_endline "yielding" ; 
     k (Obj.magic ())
  | _ -> failwith "NO MATCH"

let rec run t =
  match observe t with
  | RetF r -> r
  | TauF t -> run t
  | VisF (e, k) -> handle_Event e (fun x -> run (k x))









(* let rr_match h rr = function
 * | [] -> triggerUB h
 * | t :: ts ->
 *   (match observe t with
 *    | RetF _ -> lazy (Coq_go (TauF (rr ts)))
 *    | TauF u -> lazy (Coq_go (TauF (rr (u :: ts))))
 *    | VisF (o, k) ->
 *      lazy (Coq_go (VisF (o, (fun x -> rr (shuffle ((k x) :: ts)))))))
 * 
 * (\** val round_robin :
 *     (__ coq_Event, 'a1) coq_IFun -> ('a1, 'a2) itree list -> ('a1, 'a2) itree **\)
 * 
 * let rec round_robin h q =
 *   rr_match h (round_robin h) q
 * 
 * (\** val run_till_event_aux :
 *     ((__ coq_Event, 'a1) itree -> (__ coq_Event, 'a1) itree) -> (__
 *     coq_Event, 'a1) itree -> (__ coq_Event, 'a1) itree **\)
 * 
 * let run_till_event_aux rr q =
 *   match observe q with
 *   | RetF _ -> q
 *   | TauF u -> lazy (Coq_go (TauF (rr u)))
 *   | VisF (o, k) -> handle_Event o k
 * 
 * (\** val run_till_event :
 *     (__ coq_Event, 'a1) itree -> (__ coq_Event, 'a1) itree **\)
 * 
 * let rec run_till_event q =
 *   run_till_event_aux run_till_event q *)


let rec my_rr q =
  (my_rr_match (fun _ _ _ -> handle_Event)
     (fun q -> match q with
               | [] -> []
               | _ :: _ -> my_rr q)) q

(* let rec my_rr q =
 *   let q = my_rr_once q in
 *   let q = List.filter (fun i -> match observe i with RetF _ -> false | _ -> true) q in
 *   match q with
 *   | [] -> ()
 *   | _ :: _ -> my_rr q *)

let main =
  Random.self_init();

  (* print_endline "-----------------------------------" ;
   * run (eval_program LoadStore.program) ;
   * print_endline "-----------------------------------" ;
   * run (eval_program Rec.program) ;
   * print_endline "-----------------------------------" ;
   * run (eval_program MutRec.program) ;
   * print_endline "-----------------------------------" ;
   * run (eval_program Move.program) ;
   * print_endline "-----------------------------------" ;
   * run (eval_program CoqCode.program) ;
   * print_endline "-----------------------------------" ;
   * run (eval_program Control.program) ;
   * print_endline "-----------------------------------" ;
   * run (MultiModule.isem) ;
   * print_endline "-----------------------------------" ;
   * run (MultiModuleLocalState.isem) ; *)
  (* print_endline "-----------------------------------" ;
   * my_rr (List.map eval_program Concur.programs) ; *)
  (* print_endline "-----------------------------------------------------------" ;
   * run (round_robin (fun _ -> shuffle) (List.map eval_program MultiCore.programs)) ; *)

  if true
  then begin

  run (CoqCodeCBR.isem) ;
  print_endline "-----------------------------------------------------------" ;
  run (MultiCore2.sem) ;
  print_endline "-----------------------------------------------------------" ;
  run (MultiCoreMPSC.sem) ;
  print_endline "-----------------------------------------------------------" ;
  run (MultiModuleMultiCore.sem) ;

  print_endline "-----------------------------------------------------------" ;
  run (eval_whole_program DoubleReturn.program) ;

  print_endline "-----------------------------------------------------------" ;
  run (MultiModuleLocalStateSimple.isem1) ;
  print_endline "-----------------------------------------------------------" ;
  run (MultiModuleLocalStateSimple.isem2) ;
  print_endline "-----------------------------------------------------------" ;
  run (MultiModuleLocalStateSimpleLang.isem) ;
  print_endline "-----------------------------------------------------------" ;
  run (MultiModuleGenv.isem) ;

  print_endline "-----------------------------------------------------------" ;
  run (eval_whole_program MpoolSeq.TEST.TEST2.program) ;

  print_endline "-----------------------------------------------------------" ;
  run (eval_whole_program MpoolSeq.TEST.TEST3.program) ;

  print_endline "-----------------------------------------------------------" ;
  run (eval_whole_program MpoolSeq.TEST.TEST4.program) ;

  print_endline "-----------------------------------------------------------" ;
  run (eval_whole_program CPUSeq.CPUTEST.program) ;

  print_endline "-----------------------------------------------------------" ;
  run (MpoolConcur.TEST.TEST1.isem) ;

  print_endline "-----------------------------------------------------------" ;
  run (MpoolConcur.TEST.TEST2.isem) ;

  print_endline "-----------------------------------------------------------" ;
  run (MpoolConcur.TEST.TEST3.isem1) ;
  run (MpoolConcur.TEST.TEST3.isem2) ;

  print_endline "-----------------------------------------------------------" ;
  run (MultiModuleMultiCoreLocalState.isem) ;

  print_endline "-----------------------------------------------------------" ;
  run (PrintAny.isem) ;


  end;

  print_endline "-----------------------------------------------------------" ;
  run (MpoolConcur.TEST.TEST4.isem) ;

  print_endline "-----------------------------------------------------------" ;
  run (MMStageOne.MMTEST1.isem) ;

  print_endline "-----------------------------------------------------------" ;
  run (MMStageOne.MMTESTAUX.isem) ;

  print_endline "-----------------------------------------------------------" ;
  run (eval_whole_program MMHighStageOne.HighSpecDummyTest.program) ;

  ()
