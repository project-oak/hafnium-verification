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


Require Import Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.
Require Import BitNat.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Local Open Scope N_scope.

Module MMARCH.

  (* define root_table_count - 1 for all *)

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
   static uint64_t pte_addr(pte_t pte)
   {
       return pte & PTE_ADDR_MASK;
   }
   *)

   
  

End MMARCH.

Module MMSTAGE1.
  
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
       Debug "[alloc_page] calling mpool_alloc" Vnull #;
       res #= (Call "alloc" [CBR ppool; CBV 1]) #;
           Return res
     else
       Debug "[alloc_page] calling mpool_alloc_contiguous" Vnull #;
       res #= (Call "alloc_contiguous" [CBR ppool ; CBV count]) #;
           Return res.

  (*
  static void mm_free_page_pte(pte_t pte, uint8_t level, struct mpool *ppool)
  {
        struct mm_page_table *table;
        uint64_t i;

        if (!arch_mm_pte_is_table(pte, level)) {
                return;
        }

        /* Recursively free any subtables. */
        table = mm_page_table_from_pa(arch_mm_table_from_pte(pte, level));
        for (i = 0; i < MM_PTE_PER_PAGE; ++i) {
                mm_free_page_pte(table->entries[i], level - 1, ppool);
        }

        /* Free the table itself. */
        mpool_free(ppool, table);
  }
  *)

  Definition mm_free_page_pte (pte level ppool : var) (table is_table_v arch_mm_v i entry_loc entry_i l_arg : var) :=
    is_table_v #= (Call "arch_mm_pte_is_table" [CBV pte ; CBV level]) #;
               #if (Not is_table_v)
                then
                  Skip
                else
                  arch_mm_v #= (Call "arch_mm_table_from_pte" [CBV pte; CBV level]) #;
                            table #= (Call "mm_page_table_from_pa" [CBV arch_mm_v]) #;
                            i #= 0 #;
                            #while (i <= (MM_PTE_PER_PAGE - 1))
                            do (
                              entry_loc #= (table #@ 0) #;
                                        entry_i #= (entry_loc #@ i) #;
                                        l_arg #= (level - 1) #; 
                                        (Call "mm_free_page_pte" [CBV entry_i; CBV l_arg ; CBV ppool]) #;
                                        i #= (i + 1)
                            ).  
  
  (*
  static void mm_ptable_fini(struct mm_ptable *t, int flags, struct mpool *ppool)
  {
        struct mm_page_table *tables = mm_page_table_from_pa(t->root);
        uint8_t level = mm_max_level(flags);
        uint8_t root_table_count = mm_root_table_count(flags);
        uint8_t i;
        uint64_t j;

        for (i = 0; i < root_table_count; ++i) {
                for (j = 0; j < MM_PTE_PER_PAGE; ++j) {
                        mm_free_page_pte(tables[i].entries[j], level, ppool);
                }
        }

        mpool_add_chunk(ppool, tables,
                        sizeof(struct mm_page_table) * root_table_count);
  }
   *)

  Definition mm_ptable_fini (t flags ppool : var) (tables level root_count t_root i j i_table j_entry : var) : stmt :=
    t_root #= (t #@ 0) #;
           root_count #= (Call "mm_page_table_from_pa" [CBV t_root ]) #;
           level #= (Call "mm_max_level" [CBV flags]) #;
           root_count #= (Call "mm_root_table_count" [CBV flags]) #;
           i #= (0) #;
           #while (i  <= root_count - 1)
           do (j #= 0 #;
                 #while (j  <= MM_PTE_PER_PAGE - 1)
                 do (i_table #= (tables #@ i) #;
                             j_entry #= (i_table #@ j) #;
                             (Call "mm_free_page_pte" [CBV j_entry; CBV level; CBV ppool]) #;
                             j #= (j + 1)                        
                    ) #;
                 i #= (i + 1) 
              ).
  
  


  

  (* JIEUNG: I will work on the following things *)
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



(* Print MM_PTE_PER_PAGE. => 512 *)


Module MMTEST1.

  Include MMSTAGE1.

  (* Stack overflow... We may need to change the representation type from nat number to Z number
  Definition TEST_HEAP_SIZE := 65536%nat. *)
  Definition TEST_HEAP_SIZE := 4096%nat. 
  Definition TOP_LEVEL := 3%N.
  Definition pte_paddr_begin := 4000%N.

  Definition entry_size: nat := 4.

  (* Those things will be arguments of our multiple test cases *)
  Require Import ZArith.
  Definition VM_MEM_START: Z := 0.
  Definition VM_MEM_END: Z := 2199023255552. (* (2^16) *)

  Check (big_mem_flat pte_paddr_begin TEST_HEAP_SIZE 4).

  Definition main (p i r: var): stmt :=
    Eval compute in INSERT_YIELD (
      p #= Vptr None [0: val ; 0: val ; 0: val ] #;
        Call "MPOOLCONCUR.mpool_init" [CBR p] #;
        (* Need to refine the following definition *)
        DebugMpool "(Global Mpool) After initialize" p #;
        Call "MPOOLCONCUR.add_chunk" [CBR p ; CBV (big_mem_flat pte_paddr_begin TEST_HEAP_SIZE 4);
                                        CBV (N.of_nat TEST_HEAP_SIZE)] #;
        "GPOOL" #= p #;
        
        #while ("SIGNAL" <= 1) do (Debug "waiting for SIGNAL" Vnull) #;
        (*** JUST FOR PRINTING -- START ***)
        p #= (Call "Lock.acquire" [CBV (p #@ 0)]) #;
        DebugMpool "(Global Mpool) Final: " p #;
        (Call "Lock.release" [CBV (p #@ 0) ; CBV p]) #;
        (*** JUST FOR PRINTING -- END ***)
        i #= 10 #;
        #while i
        do (
            i #= i-1 #;
                     (Debug "[main] calling mm_alloc_page_tables" Vnull) #;      
                     r #= Call "mm_alloc_page_tables" [CBV 1 ; CBR p] #;
                     #assume r
          ) #; 
            Put "main finish" Vnull #;
            Put "MMTEST Passed" Vnull).
  
    Definition ptable_alloc (count : N)
               (p i r0 r1 r2: var): stmt := Eval compute in INSERT_YIELD (
      #while (!"GPOOL") do (Debug "waiting for GMPOOL" Vnull) #;
      p #= Vptr None [0: val ; 0: val ; 0: val ] #;
      Call "MPOOLCONCUR.init_with_fallback" [CBR p ; CBV "GPOOL"] #;
      DebugMpool "(Local Mpool) After init-with-fallback" p #;
      (* #while i *)
      (* do ( *)
      Debug "looping, i is: " i #;
      i #= i - 1 #;
        (Debug "[thread] calling mm_alloc_page_tables" Vnull) #;      
        r0 #= Call "mm_alloc_page_tables" [CBV count; CBR p] #;
        r1 #= Call "mm_alloc_page_tables" [CBV (count + 1); CBR p] #;
        r2 #= Call "mm_alloc_page_tables" [CBV (count + 2); CBR p] #;
        Skip
      (* ) #; *)
      #;
      Put "thread finish" Vnull #;
      "SIGNAL" #= "SIGNAL" + 1 #; 
      Skip).


    (*
static void mm_free_page_pte(pte_t pte, uint8_t level, struct mpool *ppool)
{
        struct mm_page_table *table;
        uint64_t i;

        if (!arch_mm_pte_is_table(pte, level)) {
                return;
        }

        /* Recursively free any subtables. */
        table = mm_page_table_from_pa(arch_mm_table_from_pte(pte, level));
        for (i = 0; i < MM_PTE_PER_PAGE; ++i) {
                mm_free_page_pte(table->entries[i], level - 1, ppool);
        }

        /* Free the table itself. */
        mpool_free(ppool, table);
}
     *)

    
    (* JIEUNG: If it is easy, I hope to add different binary operators, such as LT *)
    Definition mm_free_page_pte (pte level ppool : var)
               (table is_table_v arch_mm_v i entry_loc entry_i l_arg : var) :=
      is_table_v #= (Call "arch_mm_pte_is_table" [CBV pte ; CBV level]) #;
                 #if (Not is_table_v)
                  then
                    Skip
                  else
                    arch_mm_v #= (Call "arch_mm_table_from_pte" [CBV pte; CBV level]) #;
                              table #= (Call "mm_page_table_from_pa" [CBV arch_mm_v]) #;
                              i #= 0 #;
                              #while (i <= (MM_PTE_PER_PAGE - 1))
                              do (
                                entry_loc #= (table #@ 0) #;
                                          entry_i #= (entry_loc #@ i) #;
                                          l_arg #= (level - 1) #; 
                                          (Call "mm_free_page_pte" [CBV entry_i; CBV l_arg ;
                                                                      CBV ppool]) #;
                                          i #= (i + 1)
                              ).


    
    Definition mm_alloc_page_tablesF : function.
      mk_function_tac mm_alloc_page_tables ["count" ; "ppool"] ["res"].
    Defined.
    Definition mainF: function.
      mk_function_tac main ([]: list var) ["p" ; "i" ; "r"].
    Defined.
    Definition ptable_alloc1F: function.
      mk_function_tac (ptable_alloc 1) ([]: list var) ["p" ; "i" ; "r0" ; "r1" ; "r2"].
    Defined.
    Definition ptable_alloc2F: function.
      mk_function_tac (ptable_alloc 2) ([]: list var) ["p" ; "i" ; "r0" ; "r1" ; "r2"].
    Defined.
                                         
    Definition program: program :=
      [
        ("main", mainF) ;
      ("alloc1F", ptable_alloc1F) ;
      ("alloc2F", ptable_alloc2F) ;
      ("mm_alloc_page_tables", mm_alloc_page_tablesF)
      ].
    
    Definition modsems: list ModSem := [program_to_ModSem program ; LOCK.modsem ; MPOOLCONCUR.mpool_modsem]. 
    
    Definition isem: itree Event unit :=
      eval_multimodule_multicore
        modsems [ "main" ; "alloc1F" ; "alloc2F" ].



    
End MMTEST1.
  
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

size_t mm_entry_size(int level)
{
        return UINT64_C(1) << (PAGE_BITS + level * PAGE_LEVEL_BITS);
}

bool mm_vm_is_mapped(struct mm_ptable *t, ipaddr_t ipa)
{
        uint32_t mode;
        return mm_vm_get_mode(t, ipa, ipa_add(ipa, 1), &mode) &&
               (mode & MM_MODE_INVALID) == 0;
}


*) 
