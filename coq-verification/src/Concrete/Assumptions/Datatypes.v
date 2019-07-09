Require Import Hafnium.Util.List.

(*** This file is for datatypes that are left abstract so as to avoid making any
     assumptions about their content. It may be necessary to instantiate these
     types later. ***)

(* pointers to page tables *)
Axiom ptable_pointer : Type.

(* equality between pointers is decidable *)
Axiom ptable_pointer_eq_dec :
  forall ptr1 ptr2 : ptable_pointer, {ptr1 = ptr2} + {ptr1 <> ptr2}.

(* assume NULL exists *)
Axiom null_pointer : ptable_pointer.

(* out-of-bounds accesses to lists of ptable_pointers return null_pointer *)
Global Instance ptable_pointer_oobe : OutOfBoundsElement ptable_pointer :=
  {| oob_value := null_pointer |}.
