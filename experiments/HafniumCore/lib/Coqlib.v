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
Require Import Lists.List.
Import ListNotations.

Set Implicit Arguments.



Fixpoint filter_map A B (f: A -> option B) (l: list A): list B :=
  match l with
  | [] => []
  | hd :: tl =>
    match (f hd) with
    | Some b => b :: (filter_map f tl)
    | _ => filter_map f tl
    end
  end
.

Definition try_left A B (ab: A + B): option A :=
  match ab with
  | inl a => Some a
  | _ => None
  end
.

Definition try_right A B (ab: A + B): option B :=
  match ab with
  | inr b => Some b
  | _ => None
  end
.

Notation unwrap :=
  (fun x default => match x with
                    | Some y => y
                    | _ => default
                    end)
.

(* Notation "'unwrap' x default" := *)
(*   (match x with *)
(*    | Some y => y *)
(*    | _ => default *)
(*    end) (at level 60) *)
(* . *)

(* Definition unwrap X (x: option X) (default: X): X := *)
(*   match x with *)
(*   | Some x => x *)
(*   | _ => default *)
(*   end *)
(* . *)

Definition is_some X (x: option X): bool :=
  match x with
  | Some _ => true
  | _ => false
  end
.

Definition is_none X (x: option X): bool :=
  match x with
  | Some _ => false
  | _ => true
  end
.

Ltac apply_list f ls :=
  let rec go f ls :=
      match ls with
      | nil => f
      | ?hd :: ?tl => go (f hd) tl
      end
  in
  go f ls
.

