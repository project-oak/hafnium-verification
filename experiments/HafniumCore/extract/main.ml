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
open Lang
open MpoolSeq
open MpoolConcur
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
open Sflib

module Nat = struct
  include Nat
  let rec to_int = function | O -> 0 | S n -> succ (to_int n)
  let rec of_int n = assert(n >= 0); if(n == 0) then O else S (of_int (pred n))
end

let shuffle: 'a list -> 'a list = fun xs ->
  let xis = List.map (fun x -> (Random.bits (), x)) xs in
  let yis = List.sort (fun x0 x1 -> Stdlib.compare (fst x0) (fst x1)) xis in
  List.map snd yis

let cl2s = fun cl -> String.concat "" (List.map (String.make 1) cl)

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

let print_val = fun v -> print_endline (string_of_val v)

let string_of_vals vs = List.fold_left (fun s i -> s ^ " " ^ string_of_val i) "" vs

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

let handle_Event = fun e k ->
  match e with
  | ENB msg -> failwith ("NB:" ^ (cl2s msg))
  | EUB msg -> failwith ("UB:" ^ (cl2s msg))
  | ESyscall ('p'::[], msg, v::[]) ->
     print_string (cl2s msg) ; print_val v ; k (Obj.magic ())
  | ESyscall ('d'::[], msg, vs) ->
     (* print_string "<DEBUG> " ; print_string (cl2s msg) ;
      * print_endline (string_of_vals vs) ; *)
     k (Obj.magic ())
  | ESyscall ('g'::[], _,   []) ->
     let x = read_int() in k (Obj.magic (Vnat (Nat.of_int x)))
  | ESyscall (cl,      msg, vs) ->
     print_string (cl2s msg) ; print_endline (cl2s cl) ;
     failwith "UNSUPPORTED SYSCALL"
  | EYield ->
     (* print_endline "yielding" ; *)
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
  (my_rr_match (fun _ -> shuffle) (fun _ _ _ -> handle_Event)
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
   * run (round_robin (fun _ -> shuffle) (List.map eval_program MultiCore.programs)) ;
   * print_endline "-----------------------------------" ;
   * run (MultiModule.isem) ;
   * print_endline "-----------------------------------" ;
   * run (MultiModuleLocalState.isem) ; *)
  (* print_endline "-----------------------------------" ;
   * my_rr (List.map eval_program Concur.programs) ; *)

  print_endline "-----------------------------------------------------------" ;
  run (eval_program DoubleReturn.program) ;

  print_endline "-----------------------------------------------------------" ;
  run (MultiModuleLocalStateSimple.isem1) ;
  print_endline "-----------------------------------------------------------" ;
  run (MultiModuleLocalStateSimple.isem2) ;

  (* print_endline "-----------------------------------------------------------" ;
   * run (eval_program MpoolSeq.TEST.TEST1.program) ; *)

  print_endline "-----------------------------------------------------------" ;
  run (eval_program MpoolSeq.TEST.TEST2.program) ;

  print_endline "-----------------------------------------------------------" ;
  run (eval_program MpoolSeq.TEST.TEST3.program) ;

  print_endline "-----------------------------------------------------------" ;
  run (eval_program MpoolSeq.TEST.TEST4.program) ;

  print_endline "-----------------------------------------------------------" ;
  run (MpoolConcur.TEST.TEST1.isem) ;

  print_endline "-----------------------------------------------------------" ;
  run (MpoolConcur.TEST.TEST2.isem) ;

  print_endline "-----------------------------------------------------------" ;
  run (MpoolConcur.TEST.TEST3.isem) ;

  ()
