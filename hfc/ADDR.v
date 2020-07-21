(*
 * Copyright 2020 Jieung Kim (jieungkim@google.com)
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
Require Import Types.

Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Module ADDR.

  (*
#pragma once

#include <stddef.h>
#include <stdint.h>

#include "hf/arch/types.h"
   *)


  (*
/** An opaque type for a physical address. */
typedef struct {
        uintpaddr_t pa;
} paddr_t;

/** An opaque type for an intermediate physical address. */
typedef struct {
        uintpaddr_t ipa;
} ipaddr_t;

/** An opaque type for a virtual address. */
typedef struct {
        uintvaddr_t va;
} vaddr_t;
   *)

  (*
/**
 * Initializes a physical address.
 */
static inline paddr_t pa_init(uintpaddr_t p)
{
        return (paddr_t){.pa = p};
}
   *)

  Definition pa_init(p : var) : stmt :=
    Return p.
  
  (*
/**
 * Extracts the absolute physical address.
 */
static inline uintpaddr_t pa_addr(paddr_t pa)
{
        return pa.pa;
}
   *)

  Definition pa_addr(pa : var) : stmt :=
    Return pa.

  (*  
/**
 * Advances a physical address.
 */
static inline paddr_t pa_add(paddr_t pa, size_t n)
{
        return pa_init(pa_addr(pa) + n);
}
   *)

  Definition pa_add(pa n : var) (res: var) : stmt :=
    res #= (pa + n) #;
        Return res.

  (*
/**
 * Returns the difference between two physical addresses.
 */
static inline size_t pa_difference(paddr_t start, paddr_t end)
{
        return pa_addr(end) - pa_addr(start);
}
   *)

  Definition pa_difference(pa_start pa_end : var) (res: var) : stmt :=
    res #= (pa_end - pa_start) #;
        Return res.

  (*
/**
 * Initializes an intermeditate physical address.
 */
static inline ipaddr_t ipa_init(uintpaddr_t ipa)
{
        return (ipaddr_t){.ipa = ipa};
}
   *)

  Definition ipa_init(ipa : var) : stmt :=
    Return ipa.

  (*  
/**
 * Extracts the absolute intermediate physical address.
 */
static inline uintpaddr_t ipa_addr(ipaddr_t ipa)
{
        return ipa.ipa;
}
   *)

  Definition ipa_addr(ipa : var) : stmt :=
    Return ipa.

  (*
/**
 * Advances an intermediate physical address.
 */
static inline ipaddr_t ipa_add(ipaddr_t ipa, size_t n)
{
        return ipa_init(ipa_addr(ipa) + n);
}
   *)

  Definition ipa_add(ipa n : var) (res: var) : stmt :=
    res #= (ipa + n) #;
        Return res.
  
  (*
/**
 * Initializes a virtual address.
 */
static inline vaddr_t va_init(uintvaddr_t v)
{
        return (vaddr_t){.va = v};
}
   *)

  Definition va_init(v : var) : stmt :=
    Return v.
  
  (*  
/**
 * Extracts the absolute virtual address.
 */
static inline uintvaddr_t va_addr(vaddr_t va)
{
        return va.va;
}
   *)

  Definition va_addr(va : var) : stmt :=
    Return va.

  (*  
/**
 * Casts a physical address to a virtual address.
 */
static inline vaddr_t va_from_pa(paddr_t pa)
{
        return va_init(pa_addr(pa));
}
   *)

  Definition va_from_pa(pa : var) : stmt :=
    Return pa.

  (*  
/**
 * Casts a physical address to an intermediate physical address.
 */
static inline ipaddr_t ipa_from_pa(paddr_t pa)
{
        return ipa_init(pa_addr(pa));
}
   *)

  Definition ipa_from_pa(pa : var) : stmt :=
    Return pa.

  (*  
/**
 * Casts a virtual address to a physical address.
 */
static inline paddr_t pa_from_va(vaddr_t va)
{
        return pa_init(va_addr(va));
}
   *)

  Definition pa_from_va(va : var) : stmt :=
    Return va.

  (*  
/**
 * Casts an intermediate physical address to a physical address.
 */
static inline paddr_t pa_from_ipa(ipaddr_t ipa)
{
        return pa_init(ipa_addr(ipa));
}
   *)

  Definition pa_from_ipa(ipa : var) : stmt :=
    Return ipa.

  (*  
/**
 * Casts a pointer to a virtual address.
 */
static inline vaddr_t va_from_ptr(const void *p)
{
        return (vaddr_t){.va = (uintvaddr_t)p};
}
   *)

  (* Dongjoo: I'm not sure how to convert ptr to int and reverse with dsl language. 
This code is temporary *)

  Let va_from_ptr_aux (vs: list val): (val * list val) :=
    let retv := match vs with
                | [(Vptr (Some p_id) _)]=> Vnat (p_id)
                | _ => Vnodef
                end
    in
    (retv, nil)
  .

  Definition va_from_ptr(p : var) (res: var) : stmt :=
    res #= (CoqCode [CBV p] va_from_ptr_aux) #;
        Return res.

  (*
/**
 * Casts a virtual address to a pointer. Only use when the virtual address is
 * mapped for the calling context.
 * TODO: check the mapping for a range and return a memiter?
 */
static inline void *ptr_from_va(vaddr_t va)
{
        return (void * )va_addr(va);
}
   *)

  Let ptr_from_va_aux (vs: list val): (val * list val) :=
    let retv := match vs with
                | [(Vnat p_id)]=> Vptr (Some p_id) nil
                | _ => Vnull
                end
    in
    (retv, nil)
  .

  Definition ptr_from_va(va : var) (res: var) : stmt :=
    res #= (CoqCode [CBV va] ptr_from_va_aux) #;
        Return res.



  (* function signature *)
  Definition pa_initF : function.
    mk_function_tac pa_init ["p" ] ([]: list var).
  Defined.

  Definition pa_addrF : function.
    mk_function_tac pa_addr ["pa" ] ([]: list var).
  Defined.

  Definition pa_addF : function.
    mk_function_tac pa_add ["pa"; "n" ] ["res"].
  Defined.

  Definition pa_differenceF : function.
    mk_function_tac pa_difference ["pa_start"; "pa_end" ] ["res"].
  Defined.

  Definition ipa_initF : function.
    mk_function_tac ipa_init ["ipa"] ([]: list var).
  Defined.

  Definition ipa_addrF : function.
    mk_function_tac ipa_addr ["ipa"] ([]: list var).
  Defined.

  Definition va_initF : function.
    mk_function_tac va_init ["v"] ([]: list var).
  Defined.

  Definition va_addrF : function.
    mk_function_tac va_addr ["va"] ([]: list var).
  Defined.

  Definition va_from_paF : function.
    mk_function_tac va_from_pa ["pa"] ([]: list var).
  Defined.

  Definition ipa_from_paF : function.
    mk_function_tac ipa_from_pa ["pa"] ([]: list var).
  Defined.

  Definition pa_from_vaF: function.
    mk_function_tac pa_from_va ["va"] ([]: list var).
  Defined.

  Definition pa_from_ipaF: function.
    mk_function_tac pa_from_ipa ["ipa"] ([]:list var).
  Defined.

  Definition va_from_ptrF: function.
    mk_function_tac va_from_ptr ["p"] ["res"].
  Defined.

  Definition ptr_from_vaF: function.
    mk_function_tac ptr_from_va ["va"] ["res"].
  Defined.
  
  Definition addr_program: program :=
    [
      ("pa_init", pa_initF) ;
    ("pa_addr", pa_addrF) ;
    ("pa_add", pa_addF) ;
    ("pa_difference", pa_differenceF) ;
    ("ipa_init", ipa_initF) ;
    ("ipa_addr", ipa_addrF) ;
    ("va_init", va_initF) ;
    ("va_addr", va_addrF) ;
    ("va_from_pa", va_from_paF) ;
    ("ipa_from_pa", ipa_from_paF) ;
    ("pa_from_va", pa_from_vaF) ;
    ("pa_from_ipa", pa_from_ipaF) ;
    ("va_from_ptr", va_from_ptrF) ;
    ("ptr_from_va", ptr_from_vaF)
    ].

  Definition addr_modsem :=  program_to_ModSem addr_program.
  

End ADDR.


(**************************************************************
 ** From here, I copied jade's definitions as a reference 
 **************************************************************)

(*


(*
 * Copyright 2019 Jade Philipoom
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

Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Datatypes.

(*** This file defines (the necessary parts of) the API provided by addr.h,
     which is assumed correct for now. In order to replace this assumption with
     a proof of correctness, replace the [Axiom]s with definitions and proofs,
     leaving their types the same. ***)

Axiom ipaddr_t : Type.

Axiom paddr_t : Type.

Axiom vaddr_t : Type.

Axiom pa_init : uintpaddr_t -> paddr_t.

Axiom pa_addr : paddr_t -> uintpaddr_t.

Axiom pa_difference : paddr_t -> paddr_t -> size_t.

Axiom ipa_addr : ipaddr_t -> uintpaddr_t.

Axiom va_init : uintvaddr_t -> vaddr_t.

Axiom ipa_add : ipaddr_t -> size_t -> ipaddr_t.

Axiom va_addr : vaddr_t -> uintvaddr_t.

Axiom va_from_pa : paddr_t -> vaddr_t.

Axiom pa_from_va : vaddr_t -> paddr_t.

Axiom pa_from_ipa : ipaddr_t -> paddr_t.

Axiom ptr_from_va : vaddr_t -> list ptable_pointer.

Axiom is_aligned : uintpaddr_t -> nat (* PAGE_SIZE *) -> bool.

(* equality of the paddr_t type is decidable *)
Axiom paddr_t_eq_dec : forall (a1 a2 : paddr_t), {a1 = a2} + {a1 <> a2}.
Axiom pa_from_va_id : forall (a : paddr_t), pa_from_va (va_from_pa a) = a.
Axiom va_from_pa_id : forall (a : vaddr_t), va_from_pa (pa_from_va a) = a.
Axiom va_init_id : forall (a : vaddr_t), va_init (va_addr a) = a.
Axiom va_addr_id : forall (a : uintvaddr_t), va_addr (va_init a) = a.

 *)
