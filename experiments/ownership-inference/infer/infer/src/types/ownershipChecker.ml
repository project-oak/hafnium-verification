(*
 * Copyright (c) 2020 KAIST.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open! IStd
module F = Format
module L = Logging
module AbsPG = AbstractPointsToGraph

module Domain = AbsPG

let get_inst_type (i: Sil.instr) = 
  match i with
  | Load _ -> 
    "Load"
  | Store _ -> 
      "Store"
  | Prune _ -> 
      "Prune"
  | Call _ -> 
      "Call"
  | Metadata _ -> 
      "Meta"

(* Abstract Transfer Function for Ownership Type Inference *)
module TransferFunctions (CFG : ProcCfg.S) = struct
  module CFG = CFG
  module Domain = Domain

  (* Infer Sil IR pretty print *)
  let pp_inst fmt (node, inst) = 
    let inst_type = get_inst_type inst in
    F.fprintf fmt "%a: [%s] %a" CFG.Node.pp_id (CFG.Node.id node) inst_type (Sil.pp_instr ~print_types: true Pp.text) inst

  type extras = ProcData.no_extras

  (* Abstract Interpretation for Expressions *)
  (* TODO: implement this! *)
  let exec_expr astate exp = 
    let open Exp in
    match exp with
    | Var id -> failwith "Not implemented Yet"
    | UnOp (op, e, type_op) -> failwith "Not implemented Yet"
    | BinOp (op, e1, e2) -> failwith "Not implemented Yet"
    | Exn e -> failwith "Not implemented Yet"
    | Closure c -> failwith "Not implemented Yet"
    | Const c -> failwith "Not implemented Yet"
    | Cast (typ, e) -> failwith "Not implemented Yet"
    | Lvar v -> failwith "Not implemented Yet"
    | Lfield (e, field, typ) -> failwith "Not implemented Yet"
    | Lindex (e1, e2) -> failwith "Not implemented Yet"
    | Sizeof size -> failwith "Not implemented Yet"

  (* Abstract Interpretation for Instructions *)
  let exec_instr astate proc_data node instr =
    let open Sil in
    let node_kind = CFG.Node.kind node in
    let pname = Summary.get_proc_name proc_data.ProcData.summary in
    (* print the pre abstract state *)
    let _ = F.printf "== PRE ==\n%a\n====\n" Domain.pp astate in
    let _ = F.printf "%a\n" pp_inst (node, instr) in
    let post_astate = 
      (* TODO: Implement this! *)
      match instr with
      | Load {id; e; root_typ; typ; loc} -> astate
      | Store {e1; root_typ; typ; e2; loc} -> astate
      | Prune (e, loc, cond, if_kind) -> astate
      | Call ((ret_id, ret_typ), f, args, loc, flags) -> astate
      | Metadata instr_meta -> astate
    in
    (* print the post abstract state *)
    let _ = F.printf "== post ==\n%a\n====\n\n" Domain.pp post_astate in
    post_astate

  let pp_session_name _node fmt = F.pp_print_string fmt "Onwership type checker for C programs"
end

(* Traverse CFG in Reverse Post Order (i.e. Topological Order) *)
module Analyzer = AbstractInterpreter.MakeRPO (TransferFunctions (ProcCfg.Exceptional))

(* Checker Main *)
let checker {Callbacks.exe_env; summary} : Summary.t =
  let proc_desc = Summary.get_proc_desc summary in
  let proc_name = Procdesc.get_proc_name proc_desc in
  let proc_name_str = Procname.to_string proc_name in
  match String.equal proc_name_str "mpool_fini" with (* analyze only the mpool_fini function *)
  | true ->
      let _ = F.printf "%a\n@." Procname.pp proc_name in
      let tenv = Exe_env.get_tenv exe_env proc_name in
      let nodes = Procdesc.get_nodes proc_desc in
      let inv_map = Analyzer.exec_pdesc (ProcData.make_default summary tenv) ~initial:Domain.empty in
      (* currently, we do not store the analysis result *)
      summary
  | false ->
      summary
