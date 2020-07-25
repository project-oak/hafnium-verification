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
Require Import Coqlib sflib Coq.Arith.Peano_dec.
  

(* From HafniumCore *)
Require Import TestAux.
Require Import Lang.
Require Import Types.
Require Import MpoolConcur.
Require Import ArchMM.
Require Import Lock.
        

Import LangNotations.


Require Import Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.
Require Import BitNat.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Local Open Scope N_scope.


Section NOTATIONTEST.
  Local Close Scope itree_scope.
  Local Open Scope monad_scope.
  From ExtLib Require Import OptionMonad.
  Print Instances Monad.
  Print Instances PMonad.
  Variable oa: option nat.
  Fail Check (a <- oa ;; a).
  Local Existing Instance Monad_option | 100.
  Local Existing Instance Monad_option | 0.
  Notation "x ?? c1 !! c2" := (@pbind _ _ _ _ _ c1 (fun x => c2))
                                (at level 61, c1 at next level, right associativity).
  Fail Check ((a ?? oa !! a): option nat).
  Notation "x <- c1 ;; c2" := (@pbind _ (PMonad_Monad Monad_option) _ _ _ c1 (fun x => c2))
                                (at level 61, c1 at next level, right associativity).
  Check ((a <- oa ;; Some a): option nat).
End NOTATIONTEST.

Notation "x <- c1 ;; c2" := (@pbind _ (PMonad_Monad Monad_option) _ _ _ c1 (fun x => c2))
                              (at level 61, c1 at next level, right associativity).
Require Import Any.

Section AbsData.

  (* common definition *)

  Definition ident := N.

  Instance RelDec_ident: RelDec (@eq ident) :=
    { rel_dec := fun n0 n1 => if (N.eqb n0 n1) then true else false}.

  (* mpool *)

  Record mpool: Type :=
    mk {
        chunklist: list (nat * nat); (* paddr, limit *)
        fallback: option ident; (* mpoolid *)
      }
  .

  Definition mp_manager: Type := ident -> option mpool.
  Definition inital_mp_manager: mp_manager := fun _ => None.
  Definition mp_update (m: mp_manager) (k0: ident) (v: option mpool): mp_manager :=
    fun k1 => if rel_dec k0 k1 then v else m k1
  .

  (* The following are arch-independent page mapping modes. *)
  Inductive ModeFlag :=
  | MM_UNDEF1 (* nothing *)
  | MM_MODE_R (* read *)
  | MM_MODE_W (* write *)
  | MM_MODE_X (* execute *)
  | MM_MODE_D (* device *)
  .

  
  Inductive OwnModeFlag :=
  | MM_UNDEF2
  | MM_MODE_INVALID
  | MM_MODE_UNOWNED
  | MM_MODE_SHARED.
  
  
  (* I do not know whether this one is necessary or not 
  Inductive AccessFlag :=
  | AF_USED
  | AF_NON.
  *)

  (* This is the wrapper definition for va_addr to distinguish it with normal natural numbers *)
  Inductive va_addr :=
  | VA_ADDR (va: N).

  Inductive ipa_addr :=
  | IPA_ADDR (ipa: N).

  (* Low level functional model for mm_index *)
  (*
  Definition mm_index (addr level: var) (v  : var) : stmt :=
    v #= addr #>> (PAGE_BITS + (level * PAGE_LEVEL_BITS)) #;
      Return (v #& ((UINT64_C(1) #<< PAGE_LEVEL_BITS) - 1)).
   *)
  
  (* high-level functional model for mm_index - It is quite same. we just change the definition as a normal Coq definition  *)
  Definition h_mm_index  (va : va_addr) (level : N) : N :=
    match va with
    | VA_ADDR va' =>
      let v := (N.shiftr va' ((level * PAGE_LEVEL_BITS)%N + PAGE_BITS)%N) in
      let mask := (N.shiftl 1 PAGE_LEVEL_BITS) - 1 in
      (N.land v mask) 
    end.

  Definition va_page_bits (va: va_addr) : N :=
    match va with
    | VA_ADDR va' =>
      let mask := (N.shiftl 1 PAGE_BITS) - 1 in
      (N.land va' mask)
    end.

  Definition ipa_block_idx (level : N) (ipa : ipa_addr) : N :=
    match ipa with
    | IPA_ADDR ipa' =>
      let mask := (N.shiftl 1 PAGE_LEVEL_BITS) - 1 in
      (N.land (N.shiftr ipa' ((level * PAGE_LEVEL_BITS)%N + PAGE_BITS)%N) mask) 
    end.

  

  

  
  (*
  MM_FLAG_STAGE1
    MM_FLAG_COMMIT
    MM_FLAG_UNMAP
    MM_MODE_UNMAPPED_MASK
   *)
  
  Inductive ValidFlag :=
  | MM_VALID
  | MM_ABSENT.

  Inductive OwnedFlag :=
  | OWNED
  | UNOWEND.

  Inductive SharedFlag :=
  | EXCLUSIVE
  | SHARED.
  
  Inductive SG1Flag :=
  | SG1_STATUS (val: ValidFlag).

  Inductive SG2Flag :=
  | SG2_STATUS (val: ValidFlag) (owned: OwnedFlag) (sh: SharedFlag).


(*  in ptable_init
  tables = mm_alloc_page_tables(root_table_count, ppool);
  if (tables == NULL) {
    return false;
  }

  for (i = 0; i < root_table_count; i++) {
    for (j = 0; j < MM_PTE_PER_PAGE; j++) {
      tables[i].entries[j] =
        arch_mm_absent_pte(mm_max_level(flags));
    }
  }
 *)
  
(*
uint64_t arch_mm_mode_to_stage2_attrs(uint32_t mode)
{
  uint64_t attrs = 0;
  uint64_t access = 0;

  /*
   * Non-shareable is the "neutral" share mode, i.e., the shareability
   * attribute of stage 1 will determine the actual attribute.
   */
  attrs |= STAGE2_AF | STAGE2_SH(NON_SHAREABLE);

  /* Define the read/write bits. */
  if (mode & MM_MODE_R) {
    access |= STAGE2_ACCESS_READ;
  }

  if (mode & MM_MODE_W) {
    access |= STAGE2_ACCESS_WRITE;
  }

  attrs |= STAGE2_S2AP(access);

  /* Define the execute bits. */
  if (mode & MM_MODE_X) {
    attrs |= STAGE2_XN(STAGE2_EXECUTE_ALL);
  } else {
    attrs |= STAGE2_XN(STAGE2_EXECUTE_NONE);
  }

  /*
   * Define the memory attribute bits, using the "neutral" values which
   * give the stage-1 attributes full control of the attributes.
   */
  if (mode & MM_MODE_D) {
    attrs |= STAGE2_MEMATTR(STAGE2_DEVICE_MEMORY,
          STAGE2_MEMATTR_DEVICE_GRE);
  } else {
    attrs |= STAGE2_MEMATTR(STAGE2_WRITEBACK, STAGE2_WRITEBACK);
  }

  /* Define the ownership bit. */
  if (!(mode & MM_MODE_UNOWNED)) {
    attrs |= STAGE2_SW_OWNED;
  }

  /* Define the exclusivity bit. */
  if (!(mode & MM_MODE_SHARED)) {
    attrs |= STAGE2_SW_EXCLUSIVE;
  }

  /* Define the valid bit. */
  if (!(mode & MM_MODE_INVALID)) {
    attrs |= PTE_VALID;
  }

  return attrs;
}
*)
 
 
(*  in mm_populate_table_pte
  /* Allocate a new table. */
  ntable = mm_alloc_page_tables(1, ppool);
  if (ntable == NULL) {
    dlog_error("Failed to allocate memory for page table\n");
    return NULL;
  }

  /* Determine template for new pte and its increment. */
  if (arch_mm_pte_is_block(v, level)) {
    inc = mm_entry_size(level_below);
    new_pte = arch_mm_block_pte(level_below,
              arch_mm_block_from_pte(v, level),
              arch_mm_pte_attrs(v, level));
  } else {
    inc = 0;
    new_pte = arch_mm_absent_pte(level_below);
  }

  /* Initialise entries in the new table. */
  for (i = 0; i < MM_PTE_PER_PAGE; i++) {
    ntable->entries[i] = new_pte;
    new_pte += inc;
  }
 *)

 (*

uint32_t arch_mm_stage2_attrs_to_mode(uint64_t attrs)
{
  uint32_t mode = 0;

  if (attrs & STAGE2_S2AP(STAGE2_ACCESS_READ)) {
    mode |= MM_MODE_R;
  }

  if (attrs & STAGE2_S2AP(STAGE2_ACCESS_WRITE)) {
    mode |= MM_MODE_W;
  }

  if ((attrs & STAGE2_XN(STAGE2_EXECUTE_MASK)) ==
      STAGE2_XN(STAGE2_EXECUTE_ALL)) {
    mode |= MM_MODE_X;
  }

  if ((attrs & STAGE2_MEMATTR_TYPE_MASK) == STAGE2_DEVICE_MEMORY) {
    mode |= MM_MODE_D;
  }

  if (!(attrs & STAGE2_SW_OWNED)) {
    mode |= MM_MODE_UNOWNED;
  }

  if (!(attrs & STAGE2_SW_EXCLUSIVE)) {
    mode |= MM_MODE_SHARED;
  }

  if (!(attrs & PTE_VALID)) {
    mode |= MM_MODE_INVALID;
  }

  return mode;
}
*)


(*
uint64_t arch_mm_mode_to_stage1_attrs(uint32_t mode)
{
  uint64_t attrs = 0;

  attrs |= STAGE1_AF | STAGE1_SH(OUTER_SHAREABLE);

  /* Define the execute bits. */
  if (!(mode & MM_MODE_X)) {
    attrs |= STAGE1_XN;
  }

  /* Define the read/write bits. */
  if (mode & MM_MODE_W) {
    attrs |= STAGE1_AP(STAGE1_READWRITE);
  } else {
    attrs |= STAGE1_AP(STAGE1_READONLY);
  }

  /* Define the memory attribute bits. */
  if (mode & MM_MODE_D) {
    attrs |= STAGE1_ATTRINDX(STAGE1_DEVICEINDX);
  } else {
    attrs |= STAGE1_ATTRINDX(STAGE1_NORMALINDX);
  }

  /* Define the valid bit. */
  if (!(mode & MM_MODE_INVALID)) {
    attrs |= PTE_VALID;
  }

  return attrs;
}
*)


(*
uint64_t arch_mm_combine_table_entry_attrs(uint64_t table_attrs,
             uint64_t block_attrs)
{
  /*
   * Only stage 1 table descriptors have attributes, but the bits are res0
   * for stage 2 table descriptors so this code is safe for both.
   */
  if (table_attrs & TABLE_NSTABLE) {
    block_attrs |= STAGE1_NS;
  }
  if (table_attrs & TABLE_APTABLE1) {
    block_attrs |= STAGE1_AP2;
  }
  if (table_attrs & TABLE_APTABLE0) {
    block_attrs &= ~STAGE1_AP1;
  }
  if (table_attrs & TABLE_XNTABLE) {
    block_attrs |= STAGE1_XN;
  }
  if (table_attrs & TABLE_PXNTABLE) {
    block_attrs |= STAGE1_PXN;
  }
  return block_attrs;
}
*)

 
  
  (* Do we need them? - those two things - I will skip them at this moment
  Polymorphic Inductive upper_attrs := | up_attr (val: Type).
  Polymorphic Inductive low_attrs := | lo_attr (val : Type). *)

  
  
  Inductive PTE_TY :=
  | PTENONE
  | PTE (owner: option N) (paddr : N) (level : N) (vaddr: option N).

  Record pt_entry: Type := mkPTE {value: list PTE_TY}.

  Definition pt_manager : Type := ident -> option pt_entry.
  Definition inital_pt_manager: mp_manager := fun _ => None.
  Definition pt_update (m: pt_manager) (k0: ident) (v: option pt_entry): pt_manager :=
    fun k1 => if rel_dec k0 k1 then v else m k1
  .

End AbsData.


Module HighSpecDummyTest.
  
  Fixpoint pte_init_iter (base_addr: N) (level : N) (esize : N) (length : nat): list PTE_TY :=
    match length with
    | O => nil
    | S O => (PTE None base_addr level None)::nil
    | S n =>
      let prev := pte_init_iter base_addr level esize n in
      let len := List.length prev in 
      prev ++ (PTE None (base_addr + (esize * (N.of_nat len))) level None)::nil
    end.

  (* initialization of the pte entry *)
  Definition pte_init (vs : list val@{expr.u1}): (val@{expr.u2} * list val@{expr.u3}) :=
    let retv := match vs with
                | [(Vnat base_addr) ; (Vnat level) ; (Vnat esize) ;(Vnat len)] =>
                  unwrap (let new_ptes := pte_init_iter base_addr level esize (N.to_nat len) in
                          Some (Vabs (upcast new_ptes))
                         ) Vnodef
                | _ => Vnodef
                end
    in (retv, nil).

  (*
  Definition pte_init_aux2 (vs : list val@{expr.u1}): (val@{expr.u2} * list val@{expr.u3}) :=
    let retv := match vs with
                | [(Vabs a)] =>
                  unwrap (ptes <- downcast a pt_entry ;;
                          let new_ptes := 
                              (match ptes with
                               | mkPTE ptes_v =>
                                 match dec with
                                 | O => ptes_v (* use as it is *)
                                 | _ => pte_init ptes_v 
                                 end
                               end) in
                          Some (Vabs (upcast new_ptes))
                         ) Vnodef
                | _ => Vnodef
                end
    in (retv, nil).
    *)
  


  (* JIEUNG: strategy: 
     MPOOL and PAGE TABLE might have different structures (Is it true?)
     This prevents us to provide the same abstarct representation. 
     So, we can duplicate them. 
     we can initialize two data structures 
     1. MPOOL 
     2. PTE  
     Each one has valid field, which is a logical flag. When we use some parts of memory for page tables, 
     we will mark that part in MPOOL and PTE together.
     If it is marked, we can check PTE to see the proper value for page tables. 
     Diabling them is quite simliar 
   *)
  
  (* JIEUNG: let's make a debugging message for abs types *)
  (* JIEUNG: let's test the way to build heap *)
  (*
  Definition pte_init (d : var) res r : stmt := 
    r #= GetOwnedHeap #;
      res #= (CoqCode [CBV r ; CBV d] pte_init_aux) #;
      PutOwnedHeap r.
   *)

  Definition main res : stmt :=
    (Debug "[high-model] Calling" Vnull) #;
    res #= (CoqCode [CBV (Vnat 4000) ; CBV (Vnat 1) ; CBV (Vnat 4) ; CBV (Vnat 4)] pte_init) #;
    DebugHigh "[high-model] Calling" res #;
    DebugHigh "[high-model] Call End" res.
    (* Put "high level test end:" res. *)

  Definition mainF: function.
      mk_function_tac main ([]: list var) (["res"] : list var).
  Defined.
  
  Definition program: program :=
    [
      ("main", mainF)
    ].
  
  Definition modsems: list ModSem := [program_to_ModSem program]. 
  
  (*
    Definition isem: itree Event unit :=
      eval_multimodule_multicore
        modsems [ "main" ; "alloc1F" ; "alloc2F" ].
   *)
  
End HighSpecDummyTest.



(*
Module MPOOLMMHIGHTest.

  Let mpool_init_aux (vs: list val): (val * list val) :=
    let retv := match vs with
                | [(Vabs a) ; (Vptr (Some p_id) _)] =>
                  match downcast a mp_manager with
                  | Some mm0 => let mm1 := (mp_update mm0 p_id (Some (mk nil None))) in
                                Vabs (upcast mm1)
                  | _ => Vnodef
                  end
                | _ => Vnodef
                end
    in
    (retv, nil)
  .
  
  Definition mpool_init (p: var) r: stmt :=
    r #= GetOwnedHeap #;
      PutOwnedHeap (CoqCode [CBV r ; CBV p] mpool_init_aux) #;
      Skip
  .



  Let mp_init_with_fallback_aux (vs: list val): (val * list val) :=
    let retv := match vs with
                | [(Vabs a) ; (Vptr (Some p_id) _) ; (Vptr (Some fb_id) _)] =>
                  match downcast a mp_manager with
                  | Some mm0 => let mm1 := (mp_update mm0 p_id (Some (mk nil (Some fb_id)))) in
                                Vabs (upcast mm1)
                  | _ => Vnodef
                  end
                | _ => Vnodef
                end
    in
    (retv, nil)
  .
  
  Definition mpool_init_with_fallback (p fallback: var) r: stmt :=
    r #= GetOwnedHeap #;
      PutOwnedHeap (CoqCode [CBV r ; CBV p ; CBV fallback] mp_init_with_fallback_aux) #;
      Skip
  .
  
  Let mpool_check_fallback (vs: list val): (val * list val) :=
    let retv := match vs with
                | [(Vabs a) ; (Vptr (Some p_id) _)]=>
                  unwrap (mm <- downcast a mp_manager ;;
                          mp <- mm p_id ;;
                          Some (is_some (mp.(fallback)): val)
                         ) Vnodef
                | _ => Vnodef
                end
    in
    (retv, nil)
  .
  
  Let mpool_get_chunk_list (vs: list val): (val * list val) :=
    let retv := match vs with
                | [(Vabs a) ; (Vptr (Some p_id) _)]=>
                  unwrap (mm <- downcast a mp_manager ;;
                          mp <- mm p_id ;;
                          Some (Vabs (upcast mp.(chunklist)))
                         ) Vnodef
                | _ => Vnodef
                end
    in
    (retv, nil)
  .
  
  Definition mpool_add_chunk (mp: mpool) (chunk: nat * nat): mpool :=
    mk (chunk :: mp.(chunklist)) mp.(fallback)
  .

  Let mp_fini_aux (vs: list val): (val * list val) :=
    match vs with
    | [(Vabs a0) ; (Vptr (Some p_id) _) ; (Vabs a1)]=>
      unwrap (mm0 <- downcast a0 mp_manager ;;
              cl <- downcast a1 (list (nat * nat)) ;;
              mp <- mm0 p_id ;;
              fb_id <- mp.(fallback) ;;
              fb <- mm0 fb_id ;;
              match cl with
              | hd :: tl =>
                let mm1 := (mp_update mm0 fb_id (Some (mpool_add_chunk fb hd))) in
                Some (Vtrue, [(Vabs (upcast mm1)) ; (Vabs (upcast tl))])
              | _ => Some (Vfalse, [(Vabs a0) ; (Vabs a1)])
              (* | _ => (Vfalse, [(Vabs (upcast mm0)) ; (Vabs (upcast nil))]) *)
              end
             ) (Vnodef, nil)
    | _ => (Vnodef, nil)
    end
  .

  Let fini_aux2 (vs: list val): (val * list val) :=
    let retv := match vs with
                | [(Vabs a) ; (Vptr (Some p_id) _)]=>
                  unwrap (mm0 <- downcast a mp_manager ;;
                          mp <- mm0 p_id ;;
                          let mm1 := (mp_update mm0 p_id None) in
                          Some (Vabs (upcast mm1))
                         ) Vnodef
                | _ => Vnodef
                end
    in
    (retv, nil)
  .

End MPOOLMMHIGHTest.
*)
