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

Module MMSTAGE1.

  (***** simple functions in the module that rely on arch mm ******) 
  (*
   static struct mm_page_table *mm_page_table_from_pa(paddr_t pa)
   {
        return ptr_from_va(va_from_pa(pa));
   }
   *)

  (* JIEUNG: TODO: ptr_from_va has to be defined *)
  (*
  Definition mm_page_table_from_pa (pa : var) (tmp res : var): stmt :=
    tmp #= (Call "va_from_pa" [CBV pa]) #;
        res #= (Call "ptr_from_va" [CBV tmp]) #;
        Return res.
   *)

  (*
  static paddr_t mm_pa_start_of_next_block(paddr_t pa, size_t block_size)
  {
        return pa_init((pa_addr(pa) + block_size) & ~(block_size - 1));
  }
  *)

  (* JIEUNG: TODO: pa_addr and pa_init has to be defined *)
  (*
  Definition mm_pa_start_of_next_block (pa block_size : var) (pa_addr_res pa_init_arg pa_init_res res: var): stmt :=
    pa_addr_res #= (Call "pa_addr" [CBV pa]) #;
                pa_init_arg #= (pa_addr_res + block_size) #;
                pa_init_res #= (Call "pa_init" [CBV pa_init_arg]) #;
                res #= And pa_init_res (Not (block_size - 1)) #;
                Return res.
  *)
  
  (***** simple functions in the module that do not rely on arch mm ******) 

  (*
    static ptable_addr_t mm_round_down_to_page(ptable_addr_t addr)  
    {
        return addr & ~((ptable_addr_t)(PAGE_SIZE - 1));
    }
   *)
  
  Definition mm_round_down_to_page (addr: var) : stmt :=
    Return (addr #& (#~ (PAGE_SIZE - 1))).

  (*  
  static ptable_addr_t mm_round_up_to_page(ptable_addr_t addr)
  {
        return mm_round_down_to_page(addr + PAGE_SIZE - 1);
  }
   *)
  
  Definition mm_round_up_to_page (addr: var) : stmt :=
    Return (Call "mm_round_down_to_page" [CBV (addr + (PAGE_SIZE - 1))]).

  (*
    static size_t mm_entry_size(uint8_t level)
    {
        return UINT64_C(1) << (PAGE_BITS + level * PAGE_LEVEL_BITS);
    }
   *)

  (* JIEUNG: We may be able to ignore UINT64_C *)
  Definition mm_entry_size (level: var) :=
    Return ((UINT64_C 1) #<< (PAGE_BITS + (level * PAGE_LEVEL_BITS))).

  (*
  static ptable_addr_t mm_start_of_next_block(ptable_addr_t addr,
                                              size_t block_size)
  {
        return (addr + block_size) & ~(block_size - 1);
  }
   *)

  Definition mm_start_of_next_block (addr block_size : var): stmt :=
    Return ((addr + block_size) #& (#~ (PAGE_SIZE - 1))).

  

  (*
  static ptable_addr_t mm_level_end(ptable_addr_t addr, uint8_t level)
  {
        size_t offset = PAGE_BITS + (level + 1) * PAGE_LEVEL_BITS;

        return ((addr >> offset) + 1) << offset;
  }
   *)

  (* JIEUNG: I used some nested operations, but I think we can divide that into multiple statements in our auto-generation *)
  Definition mm_level_end (addr level : var) (offset: var): stmt :=
    offset #= (PAGE_BITS + ((level + 1) * PAGE_LEVEL_BITS)) #;
           Return (((addr #>> offset) + 1) #<< offset).

  (*
static size_t mm_index(ptable_addr_t addr, uint8_t level)
{
        ptable_addr_t v = addr >> (PAGE_BITS + level * PAGE_LEVEL_BITS);

        return v & ((UINT64_C(1) << PAGE_LEVEL_BITS) - 1);
}
   *)

  Definition mm_index (addr level: var) (v  : var) : stmt :=
    v #= addr #>> (PAGE_BITS + (level * PAGE_LEVEL_BITS)) #;
      Return (v #& ((UINT64_C(1) #<< PAGE_LEVEL_BITS) - 1)).

  
  (*
  static struct mm_page_table *mm_alloc_page_tables(size_t count,
                                                    struct mpool *ppool)
  {
          if (count == 1) {
                  return mpool_alloc(ppool);
          }

          return mpool_alloc_contiguous(ppool, count, coun t);
  }
  *)

  
  
  Definition mm_alloc_page_tables (count ppool: var) (res : var) : stmt :=
    #if (count == 1)
     then
       Debug "[alloc_page] calling mpool_alloc" Vnull #;
             res #= (Call "alloc" [CBR ppool; CBV 1]) #;
             Debug "[alloc_page] retunr value is" res #;
           Return res
     else
       Debug "[alloc_page] calling mpool_alloc_contiguous" Vnull #;
       res #= (Call "alloc_contiguous" [CBR ppool ; CBV count]) #;
       Debug "[alloc_page] retunr value is" res #;
       Return res.


  (*
  static uint8_t mm_max_level(int flags)
  {
        return (flags & MM_FLAG_STAGE1) ? arch_mm_stage1_max_level()
                                        : arch_mm_stage2_max_level();
  }
   *)


  Definition mm_max_level (flags: var) : stmt :=
    #assume (Or (flags #& MM_FLAG_STAGE1 == 4) (flags #& MM_FLAG_STAGE1 == 0)) #;
    (#if (flags #& MM_FLAG_STAGE1)
      then
        Return (Call "arch_mm_stage1_max_level" [])
      else
        Return (Call "arch_mm_stage2_max_level" [])).

  (*
  static uint8_t mm_root_table_count(int flags)
  {
        return (flags & MM_FLAG_STAGE1) ? arch_mm_stage1_root_table_count()
                                        : arch_mm_stage2_root_table_count();
  }
   *)

  Definition mm_root_table_count (flags: var) : stmt :=
    #assume (Or (flags #& MM_FLAG_STAGE1 == 4) (flags #& MM_FLAG_STAGE1 == 0)) #;
     (#if (flags #& MM_FLAG_STAGE1)
       then
        Return (Call "arch_mm_stage1_root_table_count" [])
       else
         Return (Call "arch_mm_stage2_root_table_count" [])).
  
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

   Definition DUMMY_MM_PTE_PER_PAGE := 3.
              
   Definition mm_ptable_init (ppool : var) (i tables: var) :=
     (Debug "[mm_ptable_init] start mm_ptable_init function" Vnull) #;
      tables #= (Call "MMSTAGE1.mm_alloc_page_tables" [CBV 1; CBR ppool]) #; 
      i #= 0 #;
      (Debug "[mm_ptable_init] initialize all values in the table as 0" MM_PTE_PER_PAGE) #;
      #while (i  <= DUMMY_MM_PTE_PER_PAGE)
      do (
          tables @ i #:= 0 #;  
                 i #= (i + 1)
        ) #;
          DebugShow "[mm_ptable_init] initialized" tables.


      (*
      #while (i  <= MM_PTE_PER_PAGE - 1)
      do (
               r_table #= (tables #@ 0) #;
                       r_table @ i #:= 0 #;
                       tables @ i #:= r_table #;  
                       i #= (i + 1)                                     
        ).*) (* #;
                (* This is a dummy return value, which we need to change later *)
                Return tables. *)

  Definition ptable_initF: function.
    mk_function_tac mm_ptable_init ["ppool"] ["i"; "tables"].
  Defined.
  Definition alloc_page_tablesF : function.
    mk_function_tac mm_alloc_page_tables ["count" ; "ppool"] ["res"].
  Defined.
  
  Definition mm_stage_one_program: program :=
    [
    ("MMSTAGE1.mm_alloc_page_tables", alloc_page_tablesF);
    ("MMSTAGE1.mm_ptable_init", ptable_initF)
    ].
  
  Definition mm_stage_one_modsem : ModSem := program_to_ModSem mm_stage_one_program. 
  
              
  (*
  Definition mm_ptable_init (t flags ppool : var) (i j tables root_count max_l absent_pte i_table new_entry: var) :=
    (* root_count is always 1 *)
    root_count #= (Call "mm_root_table_count" [CBV flags]) #;
               #assume (root_count == 1) #;
               tables #= (Call "mm_alloc_page_tables" [CBV root_count; CBR ppool]) #;
               #if (tables == Vnull)
                then
                  Return Vfalse
                else
                  i #= 0 #;
                    #while (i  <= root_count - 1)
                    do (
                        j #= 0 #;
                          #assume (MM_PTE_PER_PAGE == 512) #;
                          #while (j  <= MM_PTE_PER_PAGE - 1)
                          do (max_l #= (Call "mm_max_level" [CBV flags]) #;
                                    (* we set the stage as 2 in here *) 
                                    #assume (max_l == 3) #;
                                    i_table #= (tables #@ i) #;
                                    absent_pte #= (Call "arch_mm_absent_pte" [CBV max_l]) #;
                                    i_table @ j #:= absent_pte #;
                                    tables @ i #:= i_table #;
                                    j #= (j + 1)                                     
                             ) #;
                               i #= (i + 1)                                     
                      ).
  *)
  (* the following one is ignored at this moment. *)
  (* t->root = pa_init((uintpaddr_t)tables); *)
              
  
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



Module MMTESTAUX.

  (* Test auxiliary functions in mm module *)
  Include MMSTAGE1.
  Include ArchMM.

  Definition mm_round_down_to_pageF : function.
    mk_function_tac mm_round_down_to_page ["addr"] ([]: list var).
  Defined.
  
  Definition mm_round_up_to_pageF : function.
    mk_function_tac mm_round_up_to_page ["addr"] ([]: list var).
  Defined.

  Definition mm_entry_sizeF : function.
    mk_function_tac mm_entry_size ["level"] ([]: list var).
  Defined.

  Definition mm_start_of_next_blockF : function.
    mk_function_tac mm_start_of_next_block ["addr"; "block_size"] ([]: list var).
  Defined.

  Definition mm_level_endF : function.
    mk_function_tac mm_level_end ["addr"; "level"] ["offset"].
  Defined.

  Definition mm_indexF : function.
    mk_function_tac mm_index ["addr"; "level"] ["v"].
  Defined.

  Definition mm_max_levelF : function.
    mk_function_tac mm_max_level ["flag"] ([]: list var).
  Defined.

  Definition mm_root_table_countF : function.
    mk_function_tac mm_root_table_count ["flag"] ([]: list var).
  Defined.
  
  Definition main (res: var): stmt := 
    (Put "before Start Test: " Vnull) #;
       (Put "test Vnat " (Vnat 1000)) #;
       (Put "test Page Size " (PAGE_SIZE)) #;
       (Put "test Page Size - 1 " (PAGE_SIZE - 1)) #;
       (Put "test ShiftL " (ShiftL 1 12)) #;
       (Put "test ShiftR " (ShiftR 4096 10)) #;
       (Put "test BAnd " (BAnd 3 2)) #;
       (Put "test BOr " (BOr 1 2)) #;
       (Put "test BNot " (BNot 10)) #;
       (Put "test Not " (BNot (PAGE_SIZE - 1))) #;
       
       res #= Call "mm_round_down_to_page" [CBV 4852234] #;
       (Put "mm_round_down_to_page res " res) #;
       res #= Call "mm_round_up_to_page" [CBV 4852234] #;
       (Put "mm_round_up_to_page res " res) #;
       res #= Call "mm_entry_size" [CBV 2] #;
       (Put "mm_entry_size res " res) #;
       res #= Call "mm_start_of_next_block" [CBV 4852234; CBV 4096] #;
       (Put "mm_start_of_next_block res " res) #;
       res #= Call "mm_level_end" [CBV 4852234; CBV 2] #;
       (Put "mm_level_end res " res) #;
       res #= Call "mm_index" [CBV 4852234; CBV 2] #;
       (Put "mm_index res " res) #;
       res #= Call "mm_max_level" [CBV 6] #;
       (Put "mm_max_level res " res) #;       
       res #= Call "mm_root_table_count" [CBV 7] #;
       (Put "mm_root_table_count res " res) #;       
       Skip.

  Definition mainF: function.
    mk_function_tac main ([]: list var) (["res"]: list var).
  Defined.
  
  Definition mm_program: program :=
    [
      ("main", mainF) ;
    ("mm_round_down_to_page", mm_round_down_to_pageF) ;
    ("mm_round_up_to_page", mm_round_up_to_pageF) ;
    ("mm_entry_size", mm_entry_sizeF) ;
    ("mm_start_of_next_block", mm_start_of_next_blockF) ;
    ("mm_level_end", mm_level_endF) ;
    ("mm_index", mm_indexF); 
    ("mm_max_level", mm_max_levelF); 
    ("mm_root_table_count", mm_root_table_countF) 
    ].

  Definition modsems := [ program_to_ModSem mm_program ; ArchMM.arch_mm_modsem].

  Definition isem: itree Event unit :=
    eval_multimodule_multicore
      modsems [ "main" ].
  
End MMTESTAUX.

Module MMTEST1.

  Include MMSTAGE1.

  (* Stack overflow... We may need to change the representation type from nat number to Z number
  Definition TEST_HEAP_SIZE := 65536%nat. *)
  Definition TEST_HEAP_SIZE := 1024%nat. 
  Definition TOP_LEVEL := 3%N.
  Definition pte_paddr_begin := 4000%N.

  Definition entry_size: nat := 16.

  (* Those things will be arguments of our multiple test cases *)
  Require Import ZArith.
  Definition VM_MEM_START: Z := 0.
  Definition VM_MEM_END: Z := 2199023255552. (* (2^16) *)

  Check (big_mem_flat pte_paddr_begin TEST_HEAP_SIZE entry_size).

  Definition main (p i r: var): stmt :=
    Eval compute in INSERT_YIELD (
      p #= Vptr None [0: val ; 0: val ; 0: val ] #;
        Call "MPOOLCONCUR.mpool_init" [CBR p] #;
        (* Need to refine the following definition *)
        DebugMpool "(Global Mpool) After initialize" p #;
        Call "MPOOLCONCUR.add_chunk" [CBR p ; CBV (big_mem_flat pte_paddr_begin TEST_HEAP_SIZE entry_size);
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


(* Make a test for pte_free *)
Module MMTEST2.
    
  
  

End MMTEST2.






(* example for ptable_init *)
Module MMTEST3.
 
  Include MMSTAGE1.
  
  (* Stack overflow... We may need to change the representation type from nat number to Z number
  Definition TEST_HEAP_SIZE := 65536%nat. *)
  Definition TEST_HEAP_SIZE := 1024%nat. 
  Definition TOP_LEVEL := 3%N.
  Definition pte_paddr_begin := 4000%N.

  Definition entry_size: nat := 16.
  
  (* Those things will be arguments of our multiple test cases *)
  Require Import ZArith.
  Definition VM_MEM_START: Z := 0.
  Definition VM_MEM_END: Z := 2199023255552. (* (2^16) *)

  Check (big_mem_flat pte_paddr_begin TEST_HEAP_SIZE entry_size).
  
  Definition main (p r: var): stmt :=
    Eval compute in INSERT_YIELD (
      p #= Vptr None [0: val ; 0: val ; 0: val ] #;
        Call "MPOOLCONCUR.mpool_init" [CBR p] #;
        (* Need to refine the following definition *)
        DebugMpool "ptable_init: (Global Mpool) After initialize" p #;
        Call "MPOOLCONCUR.add_chunk" [CBR p ; CBV (big_mem_flat pte_paddr_begin TEST_HEAP_SIZE entry_size);
                                        CBV (N.of_nat TEST_HEAP_SIZE)] #;
        "GPOOL" #= p #;
        
        #while ("SIGNAL" <= 1) do (Debug "ptable_init:  waiting for SIGNAL" Vnull) #;
        (*** JUST FOR PRINTING -- START ***)
        p #= (Call "Lock.acquire" [CBV (p #@ 0)]) #;
        DebugMpool "(Global Mpool) Final: " p #;
        (Call "Lock.release" [CBV (p #@ 0) ; CBV p]) #;
        (*** JUST FOR PRINTING -- END ***)
        (Debug "[main] calling mm_ptable_init" Vnull) #;      
        (Call "MMSTAGE1.mm_ptable_init" [CBR p]) #;
        (* #assume r #; *) 
        Put "ptable_init: main finish" Vnull #;
        Put "ptable_init: MMTEST Passed" Vnull).
  
    Definition ptable_init (count : N)
               (p i r: var): stmt := Eval compute in INSERT_YIELD (
      #while (!"GPOOL") do (Debug "ptable_init:  waiting for GMPOOL" Vnull) #;
      p #= Vptr None [0: val ; 0: val ; 0: val ] #;
      Call "MPOOLCONCUR.init_with_fallback" [CBR p ; CBV "GPOOL"] #;
      DebugMpool "ptable_init: (Local Mpool) After init-with-fallback" p #;
      (Call "MMSTAGE1.mm_ptable_init" [CBR p]) #;
      Put "ptable_init: thread finish" Vnull #;
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
    Definition mainF: function.
      mk_function_tac main ([]: list var) ["p" ; "r"].
    Defined.
    Definition ptable_init1F: function.
      mk_function_tac (ptable_init 1) ([]: list var) ["p" ; "i" ; "r"].
    Defined.
    Definition ptable_init2F: function.
      mk_function_tac (ptable_init 2) ([]: list var) ["p" ; "i" ; "r"].
    Defined.
                                         
    Definition program: program :=
      [
        ("main", mainF) ;
      ("init1F", ptable_init1F) ;
      ("init2F", ptable_init2F) 
      ].
    
    Definition modsems: list ModSem := [program_to_ModSem program ; MMSTAGE1.mm_stage_one_modsem;
                                       LOCK.modsem ; MPOOLCONCUR.mpool_modsem]. 
    
    Definition isem: itree Event unit :=
      eval_multimodule_multicore
        modsems [ "main" ; "init1F" ; "init2F" ].

End MMTEST3.








(**************************************
 ARCHIVED - DEFINED IN DIFFERENT FILES 
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

  (* dummy *)
  Definition arch_mm_table_from_pte (pte level : var) := Return Vtrue.

End MMARCH.

Module MMARCHMODULE.

  (* Test auxiliary functions in mm module *)
  Include MMARCH.

  Definition arch_mm_stage1_max_levelF : function.
    mk_function_tac arch_mm_stage1_max_level ([]: list var) ([]: list var).
  Defined.

  Definition arch_mm_stage2_max_levelF : function.
    mk_function_tac arch_mm_stage2_max_level ([]: list var) ([]: list var).
  Defined.

  Definition arch_mm_stage1_root_table_countF : function.
    mk_function_tac arch_mm_stage1_root_table_count ([]: list var) ([]: list var).
  Defined.
  
  Definition arch_mm_stage2_root_table_countF : function.
    mk_function_tac arch_mm_stage2_root_table_count ([]: list var) ([]: list var).
  Defined.

  Definition arch_mm_table_from_pteF : function.
    mk_function_tac arch_mm_table_from_pte ["pte"; "level"]  ([]: list var).
  Defined.
  
  Definition arch_mm_program: program :=
    [
    ("arch_mm_stage1_max_level", arch_mm_stage1_max_levelF) ;
    ("arch_mm_stage2_max_level", arch_mm_stage2_max_levelF) ;
    ("arch_mm_stage1_root_table_count", arch_mm_stage1_root_table_countF) ;
    ("arch_mm_stage2_root_table_count", arch_mm_stage2_root_table_countF) ;
    ("arch_mm_table_from_pte", arch_mm_table_from_pteF) 
    ].

  Definition arch_mm_modsem := program_to_ModSem arch_mm_program.
  
End MMARCHMODULE.
******************************************************)
  
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
