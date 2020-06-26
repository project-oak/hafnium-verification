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
Require Import TestAux.
Require Import Lang.
Require Import Types.
Require Import MpoolConcur.
Require Import ArchMM.
Require Import Lock.

Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Section MMSTAGE1.

  (* dummy *)
  (*
  uint8_t arch_mm_stage1_max_level(void)
  {
      /*
       * For stage 1 we hard-code this to 2 for now so that we can
       * save one page table level at the expense of limiting the
       * physical memory to 512GB.
       */
      return 2;
  }
 *)
  
  Definition arch_mm_stage1_max_level := Return 2.

  (*
  uint8_t arch_mm_stage2_max_level(void)
  {
      return mm_s2_max_level;
  }
 *)
  
  Definition arch_mm_stage2_max_level := Return 3.

  (*
  uint8_t arch_mm_stage1_root_table_count(void)
  {
      /* Stage 1 doesn't concatenate tables. */
      return 1;
  }
  *)
  Definition arch_mm_stage1_root_table_count := Return 1.

  (*
  uint8_t arch_mm_stage2_root_table_count(void)
  {
      return mm_s2_root_table_count;
  }
  *)

  Definition arch_mm_stage2_root_table_count := Return 1.


  (* ptable is defined in mm.h file *)
  Definition ptable := "ptable".


  
  (* JIEUNG: TODO: define ptable as a big chunk here *)
  
  (*
  static struct mm_page_table *mm_alloc_page_tables(size_t count,
                                                    struct mpool *ppool)
  {
          if (count == 1) {
                  return mpool_alloc(ppool);
          }

          return mpool_alloc_contiguous(ppool, count, count);
  }
  *)
  
  Definition mm_alloc_page_tables (count ppool: var) (res : var) : stmt :=
    #if (count == 1)
     then
       res #= (Call "mpool_alloc" [CBR ppool]) #;
           Return res
     else
       res #= (Call "mpool_alloc_contiguous" [CBR ppool ; CBV count ; CBV count]) #;
           Return res.
  
  

  (* get_table *)
  
  
  
  (*
  bool mm_ptable_init(struct mm_ptable *t, int flags, struct mpool *ppool)
  {
          uint8_t i;
          size_t j;
          struct mm_page_table *tables;
          uint8_t root_table_count = mm_root_table_count(flags);
   
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
   
          /*
           * TODO: halloc could return a virtual or physical address if mm not
           * enabled?
           */
          t->root = pa_init((uintpaddr_t)tables);
   
          return true;
  }
   *)

  (* define root_table_count - 1 for all *)
  
  Definition mm_ptable_init (t flags ppool : var) (i j tables root_count max_l absent_pte i_table new_entry: var) :=
    (* condition - flag is stage 1 or 2 *)
    root_count #= (Call "mm_root_table_count" [CBV flags]) #;
               tables #= (Call "mm_alloc_page_tables" [CBV root_count; CBR ppool]) #;
               #if (tables == Vnull)
                then
                  Return Vfalse
                else
                  i #= 0 #;
                    #while (i  <= root_count - 1)
                    do (
                        j #= 0 #;
                          #while (j  <= MM_PTE_PER_PAGE - 1)
                          do (max_l #= (Call "mm_max_level" [CBV flags]) #;
                                    i_table #= (tables #@ i) #;
                                    absent_pte #= (Call "arch_mm_absent_pte" [CBV max_l]) #;
                                    i_table @ j #:= absent_pte #;
                                    tables @ i #:= i_table #;
                                    j #= (j + 1)                                     
                             ) #;
                               i #= (i + 1)                                     
                      ).



  (* JIEUNG: TODO: ignore several parts *)

  (* 
  Definition mm_init (ppool : var) (stage1_locked mm_ptable_init_res
                                                  ltb_res lte_res lrb_res lre_res ldb_res lde_res root_v res: var) : stmt :=
    stage1_locked #= (Call "mm_stage1_lock_unsafe" []) #;
                  (* JIEUNG: Am I correct for this function call? *)
                  mm_ptable_init_res #= (Call "mm_ptable_init" [CBR ptable; CBV MM_FLAGE_STAGE1; CBR ppool]) #;
                  #if mm_ptable_init_res
                   then (Call "plat_console_mm_init" [CBV stage1_locked; CBR ppool]) #;
                      (* Map each section. *)
                      ltb_res #= (Call "layout_text_begin" []) #;
                      lte_res #= (Call "layout_text_end" []) #;
                      (Call "mm_identity_map" [CBV stage1_locked; CBV ltb_res; CBV lte_res; CBV MM_MODE_X; CBR ppool]) #;
                      lrb_res #= (Call "layout_rodata_begin" []) #;
                      lre_res #= (Call "layout_rodata_end" []) #;
                      (Call "mm_identity_map" [CBV stage1_locked; CBV lrb_res; CBV lre_res; CBV MM_MODE_R; CBR ppool]) #;
                      ldb_res #= (Call "layout_data_begin" []) #;
                      lde_res #= (Call "layout_data_end" []) #;
                      (Call "mm_identity_map" [CBV stage1_locked; CBV ldb_res; CBV lde_res; CBV (Or MM_MODE_R MM_MODE_W);
                                              CBR ppool]) #;
                      root_v #= (ptable #@ 0) #;
                      res #= (Call "arch_mm_init" [CBV root_v])
                 else
                   Return Vfalse.
   *)
                       
End MMSTAGE1.

Print MM_PTE_PER_PAGE.

Module TEST.

(*
irt,gic_version=3 -cpu cortex-a57 -nographic -machine virtualization=true -kernel out/reference/qemu_aarch64_clang/hafnium.bin -initrd initrd.img -append "rdinit=/sbin/init"
NOTICE: Initialising hafnium
INFO: text: 0x40001000 - 0x40018000
INFO: rodata: 0x40018000 - 0x4001b000
INFO: data: 0x4001b000 - 0x400b3000
INFO: Supported bits in physical address: 44
INFO: Stage 2 has 4 page table levels with 1 pages at the root.
INFO: Found PSCI version: 0x2
INFO: 60 - HEAP SIZE
INFO: Memory range:  0x40000000 - 0x47ffffff
INFO: Ramdisk range: 0x44000000 - 0x44148bff
Panic: Could not find manifest in initrd.

constexpr size_t TEST_HEAP_SIZE = PAGE_SIZE * 16;
const int TOP_LEVEL = arch_mm_stage2_max_level();
const paddr_t VM_MEM_END = pa_init(0x200'0000'0000);

PAGE_SIZE = 1 << PAGE_BITS -- 12 :=> 4096
MM_PTE_PER_PAGE  512


/**
 * Calculates the size of the address space represented by a page table entry at
 * the given level.
 */
size_t mm_entry_size(int level)
{
        return UINT64_C(1) << (PAGE_BITS + level * PAGE_LEVEL_BITS);
}

/**
 * Checks whether the address is mapped in the address space.
 */
bool mm_vm_is_mapped(struct mm_ptable *t, ipaddr_t ipa)
{
        uint32_t mode;
        return mm_vm_get_mode(t, ipa, ipa_add(ipa, 1), &mode) &&
               (mode & MM_MODE_INVALID) == 0;
}


*)


  Definition TEST_HEAP_SIZE := 65536.
  Definition TOP_LEVEL := 3.

  (* Those things will be arguments of our multiple test cases *)
  Definition VM_MEM_START := 0.
  Definition VM_MEM_END := 2199023255552. (* (2^16) *)

  
  
  

End TEST.




(*

  Module TEST4.

    Definition MAX: nat := 20.
    Definition pte_paddr_begin: nat := 4000.

    Definition main (p i r: var): stmt := Eval compute in INSERT_YIELD (
      p #= Vptr None [0: val ; 0: val ; 0: val ] #;
      Call "init" [CBR p] #;
      DebugMpool "(Global Mpool) After initialize" p #;
      Call "add_chunk" [CBR p ; CBV (big_chunk pte_paddr_begin MAX) ; CBV MAX] #;
      "GMPOOL" #= p #;
      #while ("SIGNAL" <= 1) do (Debug "waiting for SIGNAL" Vnull) #;

      (*** JUST FOR PRINTING -- START ***)
      p #= (Call "Lock.acquire" [CBV (p #@ lock_ofs)]) #;
      DebugMpool "(Global Mpool) Final: " p #;
      (Call "Lock.release" [CBV (p #@ lock_ofs) ; CBV p]) #;
      (*** JUST FOR PRINTING -- END ***)

      i #= MAX #;
      #while i
      do (
        i #= i-1 #;
        r #= Call "alloc_contiguous" [CBR p ; CBV 1] #;
        #assume r
      ) #;
      Put "Test4 Passed" Vnull
    )
    .

    Definition alloc_and_free (sz: nat)
               (p i r0 r1 r2: var): stmt := Eval compute in INSERT_YIELD (
      #while (! "GMPOOL") do (Debug "waiting for GMPOOL" Vnull) #;
      (* i #= MAX #; *)
      p #= Vptr None [0: val ; 0: val ; 0: val ] #;
      Call "init_with_fallback" [CBR p ; CBV "GMPOOL"] #;
      DebugMpool "(Local Mpool) After init-with-fallback" p #;
      (* #while i *)
      (* do ( *)
        Debug "looping, i is: " i #;
        i #= i - 1 #;
        r0 #= Call "alloc_contiguous" [CBR p ; CBV sz] #;
        r1 #= Call "alloc_contiguous" [CBR p ; CBV sz] #;
        r2 #= Call "alloc_contiguous" [CBR p ; CBV sz] #;
        #assume r0 #;
        #assume r1 #;
        #assume r2 #;
        Call "add_chunk" [CBR p ; CBV r0 ; CBV sz] #;
        Call "add_chunk" [CBR p ; CBV r1 ; CBV sz] #;
        Call "add_chunk" [CBR p ; CBV r2 ; CBV sz] #;
        Skip
      (* ) #; *)
      #;
      Call "fini" [CBR p] #;
      DebugMpool "(Local Mpool) After calling fini" p #;
      "SIGNAL" #= "SIGNAL" + 1 #;
      Skip
    )
    .

    Definition mainF: function.
      mk_function_tac main ([]: list var) ["p" ; "i" ; "r"]. Defined.
    Definition alloc_and_free2F: function.
      mk_function_tac (alloc_and_free 2) ([]: list var) ["p" ; "i" ; "r0" ; "r1" ; "r2"].
    Defined.
    Definition alloc_and_free3F: function.
      mk_function_tac (alloc_and_free 3) ([]: list var) ["p" ; "i" ; "r0" ; "r1" ; "r2"].
    Defined.

    Definition program: program :=
      [
        ("main", mainF) ;
          ("alloc_and_free2", alloc_and_free2F) ;
          ("alloc_and_free3", alloc_and_free3F) ;
          ("init", initF) ;
          ("init_with_fallback", init_with_fallbackF) ;
          ("fini", finiF) ;
          ("alloc_contiguous", alloc_contiguousF) ;
          ("alloc_contiguous_no_fallback", alloc_contiguous_no_fallbackF) ;
          ("add_chunk", add_chunkF)
      ].

    Definition modsems: list ModSem := [program_to_ModSem program ; LOCK.modsem].

    Definition isem: itree Event unit :=
      eval_multimodule_multicore
        modsems [ "main" ; "alloc_and_free2" ; "alloc_and_free3" ].

  End TEST4.

*)
