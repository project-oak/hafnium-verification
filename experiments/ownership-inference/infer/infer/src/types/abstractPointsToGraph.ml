(*
 * Copyright (c) 2020 KAIST.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

module F = Format

(* Abstract Location *)
module AbstractLocation = struct
   type id = int 
  [@@deriving compare]

  type t = NamedLoc of id * Ident.name
  | AnonymLoc of id
  [@@deriving compare]

  let mk ?name id =
    match name with
    | Some s -> NamedLoc (id, s)
    | None -> AnonymLoc id

  let pp fmt al = 
    match al with
    | NamedLoc (id, s) ->
        F.fprintf fmt "%d: %a" id Ident.pp_name s
    | AnonymLoc id ->
        F.fprintf fmt "%d" id
end

(* Set of Abstract Locations *)
module AbsLocSet = PrettyPrintable.MakePPSet(AbstractLocation)

(* Structed Memory Locations: we simple denote it as a list of single locations *)
module MemStruct = struct
  type t = SingleLoc of AbstractLocation.t
  | ListLoc of AbstractLocation.t list
  [@@deriving compare]

  let mk_single_loc l = SingleLoc l

  let mk_list_loc l = ListLoc l

  let pp fmt ms = 
    match ms with
    | SingleLoc al ->
        F.fprintf fmt "[%a]" AbstractLocation.pp al
    | ListLoc al_list ->
        let fst = ref true in
        let _ = F.fprintf fmt "[" in
        List.iter ~f:(fun al -> 
          if !fst then (fst := false; F.fprintf fmt "%a" AbstractLocation.pp al)
          else F.fprintf fmt "|%a" AbstractLocation.pp al)
          al_list 
end

(* Owernship Types *)
type ownership_type = OwnedRef 
| MutableRef of AbsLocSet.t
| SharedRef
| ShadowedRef of AbsLocSet.t
| InvalidRef
[@@deriving compare]

let pp_ownership_type fmt ot = 
  match ot with
  | OwnedRef -> F.fprintf fmt "Owned" 
  | MutableRef ls -> F.fprintf fmt "Mut borrowed from { %a }" AbsLocSet.pp ls
  | SharedRef -> F.fprintf fmt "Shared" 
  | ShadowedRef ls -> F.fprintf fmt "Shadowed by { %a }" AbsLocSet.pp ls
  | InvalidRef -> F.fprintf fmt "Invalid"

(* Edge is a triple of src, label, and dst *)
module Edge = struct
  type t = AbstractLocation.t * ownership_type * MemStruct.t
  [@@deriving compare]

  let pp fmt (al, ot, ms) = 
    begin 
      F.fprintf fmt "%a " AbstractLocation.pp al;
      F.fprintf fmt "- %a ->" pp_ownership_type ot;
      F.fprintf fmt "%a" MemStruct.pp ms
    end
end

(* Set of Edges *)
module EdgeSet = PrettyPrintable.MakePPSet(Edge)

(* Type of AbsPG *)
type t = { nodes: AbsLocSet.t ; edges: EdgeSet.t }
[@@deriving compare]

(* Node index *)
let id_index = ref 1

(* Generate a new node index *)
let new_index = 
  let index = !id_index in
  begin 
    id_index := index + 1;
    index
  end

let create_node var abspg =
  let index = new_index in
  let new_node = AbstractLocation.mk ~name:var index in
  let abspg' = { abspg with nodes = AbsLocSet.add new_node abspg.nodes } in
  new_node, abspg'

let find_or_create_node var {nodes;edges} = 
  match AbsLocSet.find_first_opt (function NamedLoc (_, var') -> Ident.equal_name var var' | _ -> false) nodes with
  | Some n -> n, {nodes;edges}
  | None -> create_node var {nodes;edges}
  
let pp fmt { edges } = EdgeSet.pp fmt edges

let empty = { nodes = AbsLocSet.empty ; edges = EdgeSet.empty }

(* Functions for Abstract Domain *)
(* TODO: implement this! *)
let leq ~lhs ~rhs = true

(* TODO: implement this! *)
let join pg1 pg2 = pg2

(* TODO: implement this! *)
let widen ~prev ~next ~num_iters = next
