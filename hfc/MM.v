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
Require Import MpoolConcur.
Require Import ArchMM.

Import LangNotations.

Require Import Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.
Require Import BitNat.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Local Open Scope N_scope.


Section MM.


(* Some dependencies: 
   1. inc/hf/addr.h - some address translations and type definitions such as paddr_t and so on 
   2. inc/hf/arch/cpu.h - 5 depends on this file
   3. src/arch/arch64/cpu.c - 5 depends on this file
   4. inc/hf/arch/mm.h - a header file for 4. 
   5. src/arch/arch64/mm.c - several simple functions are used in src/mm.c
   6. inc/hf/mm.h - a header file for this mm.c
*)

(*
struct mm_page_table {
        alignas(PAGE_SIZE) pte_t entries[MM_PTE_PER_PAGE];
};
static_assert(sizeof(struct mm_page_table) == PAGE_SIZE,
              "A page table must take exactly one page.");
static_assert(alignof(struct mm_page_table) == PAGE_SIZE,
              "A page table must be page aligned.");
*)

(* entries -> 0 *)
Definition mm_page_table : var := "mm_page_table".

(*
struct mm_ptable {
        /** Address of the root of the page table. */
        paddr_t root;
};
 *)

(* root -> 0 *)
Definition mm_ptable : var := "mm_ptable".

(*
/** The type of addresses stored in the page table. */
typedef uintvaddr_t ptable_addr_t;

/** Represents the currently locked stage-1 page table of the hypervisor. */
struct mm_stage1_locked {
        struct mm_ptable *ptable;
};
 *)

(* JIEUNG : I am not sure about this code  *)
Definition mm_stage1_locked : var := "mm_stage1_locked".

  
 (*
static struct mm_ptable ptable;
static struct spinlock ptable_lock;
  *)


Definition patble : var := "ptable".
Definition ptable_lock : var := "ptable_lock".

(*
static bool mm_stage2_invalidate = false;
 *)

Definition mm_stage2_invalidate : var := "mm_stage2_invalidate".


(*
void mm_vm_enable_invalidation(void)
{
        mm_stage2_invalidate = true;
}
 *)


Definition mm_vm_enable_invalidation : stmt :=
  mm_stage2_invalidate #= #true.

(*
static struct mm_page_table *mm_page_table_from_pa(paddr_t pa)
{
        return ptr_from_va(va_from_pa(pa));
}
*)

(* TODO: ptr_from_va has to be defined *)
Definition mm_page_table_from_pa (pa : var) (tmp res : var): stmt :=
  tmp #= (Call "va_from_pa" [CBV pa]) #;
      res #= (Call "ptr_from_va" [CBV tmp]) #;
      Return res.

(*
static ptable_addr_t mm_round_down_to_page(ptable_addr_t addr)
{
        return addr & ~((ptable_addr_t)(PAGE_SIZE - 1));
}
 *)

(* JIEUNG: It seems, we convert all types as var ... I think it is somewhat confusing. *)
Definition mm_round_down_to_page (addr: var) (res : var) : stmt :=
  Return (And addr (Not (PAGE_SIZE - 1))).

(*  
static ptable_addr_t mm_round_up_to_page(ptable_addr_t addr)
{
        return mm_round_down_to_page(addr + PAGE_SIZE - 1);
}
*)

Definition mm_round_up_to_page (addr: var) (arg res: var) : stmt :=
  arg #= (addr + (PAGE_SIZE - 1)) #;
      res #= (Call "mm_round_down_to_page" [CBV arg]) #;
      Return res.

(*
static size_t mm_entry_size(uint8_t level)
{
        return UINT64_C(1) << (PAGE_BITS + level * PAGE_LEVEL_BITS);
}
 *)

(* JIEUNG: We may be able to ignore UINT64_C *)
Definition mm_entry_size (level: var) (res: var) :=
  res #= ShiftL (UINT64_C 1) (PAGE_BITS + (level * PAGE_LEVEL_BITS)) #;
      Return res.



(* JIEUNG: many values from here (e.g. ptable_addr_t) looks memory addresses.... I ignore them in this version 
   but, I think we cannot use normal arithmatic operations in here if we want to insist value passing semantics *)
(*
static ptable_addr_t mm_start_of_next_block(ptable_addr_t addr,
                                            size_t block_size)
{
        return (addr + block_size) & ~(block_size - 1);
}
*)

Definition mm_start_of_next_block (addr block_size : var) (res: var): stmt :=
  res #= And (addr + block_size) (Not (PAGE_SIZE - 1)) #;
      Return res.

(*
static paddr_t mm_pa_start_of_next_block(paddr_t pa, size_t block_size)
{
        return pa_init((pa_addr(pa) + block_size) & ~(block_size - 1));
}
*)

Definition mm_pa_start_of_next_block (pa block_size : var) (pa_addr_res pa_init_arg pa_init_res res: var): stmt :=
  pa_addr_res #= (Call "pa_addr" [CBV pa]) #;
              pa_init_arg #= (pa_addr_res + block_size) #;
              pa_init_res #= (Call "pa_init" [CBV pa_init_arg]) #;
              res #= And pa_init_res (Not (block_size - 1)) #;
              Return res.
       

(*
static ptable_addr_t mm_level_end(ptable_addr_t addr, uint8_t level)
{
        size_t offset = PAGE_BITS + (level + 1) * PAGE_LEVEL_BITS;

        return ((addr >> offset) + 1) << offset;
}
 *)

(* JIEUNG: I used some nested operations, but I think we can divide that into multiple statements in our auto-generation *)
Definition mm_level_end (addr level : var) (offset res: var): stmt :=
  offset #= (PAGE_BITS + ((level + 1) * PAGE_LEVEL_BITS)) #;
         res #= (ShiftL ((ShiftR addr offset) + 1) offset) #;
         Return res.

(*
static size_t mm_index(ptable_addr_t addr, uint8_t level)
{
        ptable_addr_t v = addr >> (PAGE_BITS + level * PAGE_LEVEL_BITS);

        return v & ((UINT64_C(1) << PAGE_LEVEL_BITS) - 1);
}
 *)

Definition mm_index (addr level: var) (v res : var) : stmt :=
  v #= ShiftR addr (PAGE_BITS + (level * PAGE_LEVEL_BITS)) #;
    res #= And v ((ShiftL (UINT64_C(1)) PAGE_LEVEL_BITS) - 1) #;
    Return res.
  
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

(*
static uint8_t mm_max_level(int flags)
{
        return (flags & MM_FLAG_STAGE1) ? arch_mm_stage1_max_level()
                                        : arch_mm_stage2_max_level();
}
 *)


Definition mm_max_level (flags: var) (res : var) : stmt :=
  (#if (And flags MM_FLAGE_STAGE1)
    then
      res #= (Call "arch_mm_stage1_max_level" [])
    else
      res #= (Call "arch_mm_stage2_max_level" [])) #;
                                                   Return res.
  
(*
static uint8_t mm_root_table_count(int flags)
{
        return (flags & MM_FLAG_STAGE1) ? arch_mm_stage1_root_table_count()
                                        : arch_mm_stage2_root_table_count();
}
 *)

Definition mm_root_table_count (flags: var) (res : var) : stmt :=
  (#if (And flags MM_FLAGE_STAGE1)
    then
      res #= (Call "arch_mm_stage1_root_table_count" [])
    else
      res #= (Call "arch_mm_stage2_root_table_count" [])) #;
                                                          Return res.


 (*
static void mm_invalidate_tlb(ptable_addr_t begin, ptable_addr_t end, int flags)
{
        if (flags & MM_FLAG_STAGE1) {
                arch_mm_invalidate_stage1_range(va_init(begin), va_init(end));
        } else {
                arch_mm_invalidate_stage2_range(ipa_init(begin), ipa_init(end));
        }
}
  *)

(* JIEUNG: we still have several problems in here... begin and end are not normal values, but memory addresses *)
Definition mm_invalidate_tlb (begin_v end_v flags: var) (va_init_b_res va_init_e_res res : var) :=
  #if (And flags MM_FLAG_STAGE1)
   then
     va_init_b_res #= (Call "va_init" [CBV begin_v]) #;
                   va_init_e_res #= (Call "va_init" [CBV end_v]) #;
                   res #= (Call "arch_mm_invalidate_stage1_range" [CBV va_init_b_res; CBV va_init_e_res])
   else
     va_init_b_res #= (Call "ipa_init" [CBV begin_v]) #;
                   va_init_e_res #= (Call "ipa_init" [CBV end_v]) #;
                   res #= (Call "arch_mm_invalidate_stage2_range" [CBV va_init_b_res; CBV va_init_e_res]).

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
ptable_addr_t mm_ptable_addr_space_end(int flags)
{                                                       
        return mm_root_table_count(flags) * mm_entry_size(mm_max_level(flags) + 1);
}
*)

Definition  mm_ptable_addr_space_end (flags: var) (root_count entry_size res: var) : stmt := 
  root_count #= (Call "mm_root_table_count" [CBV flags]) #;
             entry_size #= (Call "mm_entry_size" [CBV flags]) #;
             res #= (root_count  * entry_size + 1) #;
             Return res.
  
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

Definition mm_ptable_init (t flags ppool : var) (i j tables root_count max_l absent_pte i_table new_entry: var) :=
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
            
            
(*
static void mm_replace_entry(ptable_addr_t begin, pte_t *pte, pte_t new_pte,
                             uint8_t level, int flags, struct mpool *ppool)
{
        pte_t v = *pte;

        if (((flags & MM_FLAG_STAGE1) || mm_stage2_invalidate) &&
            arch_mm_pte_is_valid(v, level) &&
            arch_mm_pte_is_valid(new_pte, level)) {
                *pte = arch_mm_absent_pte(level);
                mm_invalidate_tlb(begin, begin + mm_entry_size(level), flags);
        }

        /* Assign the new pte. */
        *pte = new_pte;

        /* Free pages that aren't in use anymore. */
        mm_free_page_pte(v, level, ppool);
}
 *)

Definition mm_replace_entry (begin_v pte new_pte level flags ppool: var)
           (v valid1 valid2 flag_v size_v mm_level begin_plus : var) : stmt :=
  v #= pte #;
    flag_v #= (And flags MM_FLAG_STAGE1) #;
    valid1 #= (Call "arch_mm_pte_is_valid" [CBR v; CBV level]) #;
    valid2 #= (Call "arch_mm_pte_is_valid" [CBV new_pte; CBV level]) #;
    
    (* we can define and use binary operators in here later *)
    #if (flag_v)
     then
       #if (valid1)
        then
          #if (valid2) 
           then pte #= (Call "arch_mm_absent_pte" [CBV level]) #;
                    mm_level #= (Call "mm_entry_size" [CBV level]) #;
                    begin_plus #= (begin_v + mm_level) #;
                    (Call "mm_invalidate_tlb" [CBV begin_v; CBV begin_plus; CBV flags])
           else Skip
        else Skip             
     else 
       #if (mm_stage2_invalidate)
        then
          #if (valid1)
           then
             #if (valid2) 
              then pte #= (Call "arch_mm_absent_pte" [CBV level]) #;
                       mm_level #= (Call "mm_entry_size" [CBV level]) #;
                       begin_plus #= (begin_v + mm_level) #;
                       (Call "mm_invalidate_tlb" [CBV begin_v; CBV begin_plus; CBV flags])
              else Skip
           else Skip
        else 
          Skip
            #;
            pte #= new_pte #;
            (Call "mm_free_page_pte" [CBR v; CBV level; CBV ppool]).
  
  
(*
static struct mm_page_table *mm_populate_table_pte(ptable_addr_t begin,
                                                   pte_t *pte, uint8_t level,
                                                   int flags,
                                                   struct mpool *ppool)
{
        struct mm_page_table *ntable;
        pte_t v = *pte;
        pte_t new_pte;
        size_t i;
        size_t inc;
        uint8_t level_below = level - 1;

        /* Just return pointer to table if it's already populated. */
        if (arch_mm_pte_is_table(v, level)) {
                return mm_page_table_from_pa(arch_mm_table_from_pte(v, level));
        }

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

        /* Ensure initialisation is visible before updating the pte. */
        atomic_thread_fence(memory_order_release);

        /* Replace the pte entry, doing a break-before-make if needed. */
        mm_replace_entry(begin, pte,
                         arch_mm_table_pte(level, pa_init((uintpaddr_t)ntable)),
                         level, flags, ppool);

        return ntable;
}
*)

(* JIEUNG: What is memory_order_release *)
(* JIEUNG: here, we have arithmetic opeartions on pointers again (new_pte += inc) *)

Definition  memory_order_release := "memory_order_release".

Definition mm_populate_table_pte (begin_v pte level flags ppool : var)
           (v ntable pte new_pte i inc level_below  arch_is_table arch_table res arch_is_block
              arch_block arch_attr entries i pa_init_v arch_mm_table:var) :=
  v #= pte #;
    level_below #= (level - 1) #;
    arch_is_table #= (Call "arch_mm_pte_is_table" [CBR v; CBV level]) #;
    #if (arch_is_table)
     then
       arch_table #= (Call "arch_mm_table_from_pte" [CBR v; CBV level]) #;
                  res #= (Call "mm_page_table_from_pa" [CBV arch_table]) #;
                  Return res
     else
       ntable #= (Call "mm_alloc_page_tables" [CBV (Vnat 1); CBV ppool]) #;
              #if (ntable == Vnull)
               then Return Vnull
               else
                 arch_is_block #= (Call "arch_mm_pte_is_block" [CBR v; CBV level]) #;
                               (#if (arch_is_block)
                                 then
                                   inc #= (Call "mm_entry_size" [CBV level_below]) #;
                                       arch_block #= (Call "arch_mm_block_from_pte" [CBR v; CBV level]) #;
                                       arch_attr #= (Call "arch_mm_pte_attrs" [CBR v; CBV level]) #;
                                       new_pte #= (Call "arch_mm_block_pte" [CBV level_below;
                                                                            CBV arch_block; CBV arch_attr])
                                 else
                                   inc #= 0 #;
                                       new_pte #= (Call "arch_mm_absent_pte" [CBV level_below])) #;
                               i #= 0 #;
                               #while (i <= MM_PTE_PER_PAGE - 1)
                               do (
                                   entries #= (ntable #@ 0) #;
                                           entries @ i #:= new_pte #;
                                           ntable @ 0 #:= entries #;
                                           new_pte #= (new_pte + inc) #;
                                           i #= (i + 1)
                                 ) #;
                                   (* JIEUNG: what is memory_order_release *)
                                   (Call "atomic_thread_fence" [CBV memory_order_release]) #;
                                   pa_init_v #= (Call "pa_init" [CBV ntable]) #;
                                   arch_mm_table #= (Call "arch_mm_table_pte" [CBV level; CBV pa_init_v]) #;
                                   (Call "mm_replace_entry" [CBV begin_v ; CBV pte; CBV arch_mm_table ;
                                                            CBV level ; CBV flags; CBV ppool]) #;
                                   Return ntable.
                                  
(*  
static bool mm_map_level(ptable_addr_t begin, ptable_addr_t end, paddr_t pa,
                         uint64_t attrs, struct mm_page_table *table,
                         uint8_t level, int flags, struct mpool *ppool)
{
        pte_t *pte = &table->entries[mm_index(begin, level)];
        ptable_addr_t level_end = mm_level_end(begin, level);
        size_t entry_size = mm_entry_size(level);
        bool commit = flags & MM_FLAG_COMMIT;
        bool unmap = flags & MM_FLAG_UNMAP;

        /* Cap end so that we don't go over the current level max. */
        if (end > level_end) {
                end = level_end;
        }

        /* Fill each entry in the table. */
        while (begin < end) {
                if (unmap ? !arch_mm_pte_is_present( *pte, level)
                          : arch_mm_pte_is_block( *pte, level) &&
                                    arch_mm_pte_attrs( *pte, level) == attrs) {
                } else if ((end - begin) >= entry_size &&
                           (unmap || arch_mm_is_block_allowed(level)) &&
                           (begin & (entry_size - 1)) == 0) {
                        if (commit) {
                                pte_t new_pte =
                                        unmap ? arch_mm_absent_pte(level)
                                              : arch_mm_block_pte(level, pa,
                                                                  attrs);
                                mm_replace_entry(begin, pte, new_pte, level,
                                                 flags, ppool);
                        }
                } else {
                        struct mm_page_table *nt = mm_populate_table_pte(
                                begin, pte, level, flags, ppool);
                        if (nt == NULL) {
                                return false;
                        }

                        if (!mm_map_level(begin, end, pa, attrs, nt, level - 1,
                                          flags, ppool)) {
                                return false;
                        }
                }

                begin = mm_start_of_next_block(begin, entry_size);
                pa = mm_pa_start_of_next_block(pa, entry_size);
                pte++;
        }

        return true;
}
 *)


(* JIEUNG: here, we have arithmetic opeartions on pointers again (pte++) *)
Definition mm_map_level (begin_v end_v pa attrs table level flags ppool: var)
            (mm_index_v entries pte level_end entry_size commit unmap arch_is_present arch_is_block arch_attrs
                        b_res arch_allowed cond1 cond2 cond3 cond new_pte nt mm_map_level_v end_m_begin: var) :=
   mm_index_v #= (Call "mm_index" [CBV begin_v; CBV level]) #;
              entries #= (table #@ 0) #;
              pte #= (entries #@ mm_index_v) #;
              level_end #= (Call "mm_level_end" [CBV begin_v; CBV end_v]) #;
              entry_size #= (Call "mm_entry_size" [CBV level]) #;
              commit #= (And flags MM_FLAG_COMMIT) #;
              unmap #= (And flags MM_FLAG_UNMAP) #;
              
              (#if (end_v <= level_end)
                then Skip
                else end_v #= level_end) #;
              
              (* JIEUNG: Need to fix this item *)
              #while (begin_v <= end_v - 1)
              do (arch_is_present #= (Call "arch_mm_pte_is_present" [CBV pte; CBV level]) #;
                                  arch_is_block #= (Call "arch_mm_pte_is_block" [CBV pte; CBV level]) #;
                                  arch_attrs #= (Call "arch_pte_attrs" [CBV pte ; CBV level]) #;
                                  (#if (unmap)
                                    then (#if (arch_is_present) then b_res #= Vfalse else b_res #= Vtrue)
                                    else (#if (arch_is_block)
                                           then #if (arch_attrs == attrs)
                                                 then b_res #= Vtrue
                                                 else b_res #= Vfalse
                                           else b_res #= Vfalse)) #;
                                  (#if (b_res)
                                    then Skip
                                    else
                                      end_m_begin #= (end_v - begin_v) #;
                                                  arch_allowed #= (Call "arch_mm_is_block_allowed" [CBV level]) #;
                                                  (#if (entry_size <= end_m_begin) then cond1 #= Vtrue
                                                    else cond1 #= Vfalse) #;
                                                  (#if (unmap) then cond2 #= Vtrue else
                                                      #if (arch_allowed) then cond2 #= Vtrue else cond2 #= Vfalse) #;
                                                  (#if ((And begin_v (entry_size - 1)) == 0)
                                                    then cond3 #= Vtrue else cond3 #= Vfalse) #;
                                                  (#if cond1 then
                                                      #if cond2 then
                                                         #if cond3 then cond #= Vtrue else cond #= Vfalse
                                                       else cond #= Vfalse else cond #= Vfalse) #;
                                                  #if (cond) then
                                                     (#if (commit)
                                                       then
                                                         (#if (unmap)
                                                           then new_pte #= (Call "arch_mm_absent_pte" [CBV level])
                                                           else new_pte #= (Call "arch_mm_block_pte" [CBV level ;
                                                                                                     CBV pa ;
                                                                                                     CBV attrs])) #;
                                                         (Call "mm_replace_entry" [CBV begin_v; CBR pte;
                                                                                  CBR new_pte; CBV level;
                                                                                  CBV flags; CBR ppool])
                                                       else Skip)
                                                   else
                                                     nt #= (Call "mm_populate_table_pte" [CBV begin_v; CBV pte;
                                                                                         CBV level; CBV flags;
                                                                                         CBR ppool]) #;
                                                        (#if (nt == Vnull)
                                                          then Return Vfalse
                                                          else Skip) #;
                                                        mm_map_level_v #= (Call "mm_map_level" [CBV begin_v; CBV end_v;
                                                                                               CBV pa; CBV attrs;
                                                                                               CBV nt; CBV (level - 1);
                                                                                               CBV flags; CBR ppool]) #;
                                                        (#if mm_map_level_v
                                                          then Skip
                                                          else Return Vfalse)) #;
                                  begin_v #= (Call "mm_start_of_next_block" [CBV begin_v; CBV entry_size]) #;
                                  pa #= (Call "mm_pa_start_of_next_block" [CBV pa; CBV entry_size]) #;
                                  pte #= (pte + 1)).
  
(*
static bool mm_map_root(struct mm_ptable *t, ptable_addr_t begin,
                        ptable_addr_t end, uint64_t attrs, uint8_t root_level,
                        int flags, struct mpool *ppool)
{
        size_t root_table_size = mm_entry_size(root_level);
        struct mm_page_table *table =
                &mm_page_table_from_pa(t->root)[mm_index(begin, root_level)];

        while (begin < end) {
                if (!mm_map_level(begin, end, pa_init(begin), attrs, table,
                                  root_level - 1, flags, ppool)) {
                        return false;
                }
                begin = mm_start_of_next_block(begin, root_table_size);
                table++;
        }

        return true;
}
 *)

                 
(* JIEUNG: Again, we have some arithmetic opreations... table++ ?? *) 
Definition mm_map_root (t begin_v end_v attrs root_level flags ppool : var)
           (root_size table mm_index_v root_l mm_table_res pa_init_v root_l mm_map : var) := 
  root_size #= (Call "mm_entry_size" [CBV root_level]) #;
            mm_index_v #= (Call "mm_index" [CBV begin_v; CBV root_level]) #;
            root_l #= (t #@ 0) #;
            mm_table_res #= (Call "mm_page_table_from_pa" [CBV root_l]) #;
            table #= (mm_table_res #@ mm_index_v) #;
            #while (begin_v <= end_v - 1)
            do (pa_init_v #= (Call "pa_init" [CBV begin_v]) #;
                          root_l #= (root_level - 1) #;
                          mm_map #= (Call "mm_map_level" [CBV begin_v ; CBV end_v ; CBV pa_init_v ; CBV attrs ;
                                                         CBR table ; CBV root_l ; CBV flags ; CBR ppool]) #;
                          #if (Not mm_map)
                           then Return Vfalse
                           else begin_v #= (Call "mm_start_of_next_block" [CBV begin_v ; CBV root_size]) #;
                                        table #= (table + 1)
               ) #;
                 Return (Vtrue).
               
                  
(*  
static bool mm_ptable_identity_map(struct mm_ptable *t, paddr_t pa_begin,
                                   paddr_t pa_end, uint64_t attrs, int flags,
                                   struct mpool *ppool)
{
        uint8_t root_level = mm_max_level(flags) + 1;
        ptable_addr_t ptable_end = mm_ptable_addr_space_end(flags);
        ptable_addr_t end = mm_round_up_to_page(pa_addr(pa_end));
        ptable_addr_t begin = pa_addr(arch_mm_clear_pa(pa_begin));

        CHECK(root_level >= 2);

        /* Cap end to stay within the bounds of the page table. */
        if (end > ptable_end) {
                end = ptable_end;
        }

        if (!mm_map_root(t, begin, end, attrs, root_level, flags, ppool)) {
                return false;
        }

        /* Invalidate the TLB. */
        if ((flags & MM_FLAG_COMMIT) &&
            ((flags & MM_FLAG_STAGE1) || mm_stage2_invalidate)) {
                mm_invalidate_tlb(begin, end, flags);
        }

        return true;
}
*)

Definition mm_ptable_identity_map (t pa_begin_v pa_end_v attrs flags ppool: var)
           (root_level ptable_end end_v begin_v max_v mm_map_root_v pa_addr_v arch_clear_pa_v
                       flag_commit flag_stage1 : var) := 
  max_v #= (Call "mm_max_level" [CBV flags]) #;
        root_level #= (max_v + 1) #;
        ptable_end #= (Call "mm_ptable_addr_space_end" [CBV flags]) #;
        pa_addr_v #= (Call "pa_addr" [CBV pa_end_v]) #;
        end_v #= (Call "mm_round_up_to_page" [CBV pa_addr_v]) #;
        arch_clear_pa_v #= (Call "arch_mm_clear_pa" [CBV pa_begin_v]) #;
        begin_v #= (Call "pa_addr" [CBV arch_clear_pa_v]) #;
        (#if (end_v <= ptable_end)
          then Skip
          else end_v #= ptable_end) #;
        mm_map_root_v #= (Call "mm_map_root" [CBR t; CBV begin_v; CBV end_v; CBV attrs ;
                                             CBV root_level ; CBV flags ; CBR ppool]) #;
        (#if (mm_map_root_v == Vtrue)
          then Return Vfalse
          else Skip) #;
        flag_commit #= (And flags MM_FLAG_COMMIT) #;
        flag_stage1 #= (And flags MM_FLAG_STAGE1) #;
        (#if flag_commit
          then
            #if flag_stage1
             then 
               (Call "mm_invalid_tlb" [CBV begin_v ; CBV end_v ; CBV flags])
             else
               #if mm_stage2_invalidate
                then
                  (Call "mm_invalid_tlb" [CBV begin_v ; CBV end_v ; CBV flags])                  
                else
                  Skip
          else Skip) #;
        Return Vtrue.
        
  

(*  
static bool mm_ptable_identity_prepare(struct mm_ptable *t, paddr_t pa_begin,
                                       paddr_t pa_end, uint64_t attrs,
                                       int flags, struct mpool *ppool)
{
        flags &= ~MM_FLAG_COMMIT;
        return mm_ptable_identity_map(t, pa_begin, pa_end, attrs, flags, ppool);
}
 *)


Definition mm_ptable_indentity_prepare (t pa_begin pa_end attrs flags ppool : var) (res : var) :=
  flags #= (And flags (Not MM_FLAG_COMMIT)) #;
        res #= (Call "mm_ptable_identity_map" [CBR t ; CBV pa_begin ; CBV pa_end ; CBV attrs ; CBV flags ; CBR ppool]) #;
        Return res.


(*
static void mm_ptable_identity_commit(struct mm_ptable *t, paddr_t pa_begin,
                                      paddr_t pa_end, uint64_t attrs, int flags,
                                      struct mpool *ppool)
{
        CHECK(mm_ptable_identity_map(t, pa_begin, pa_end, attrs,
                                     flags | MM_FLAG_COMMIT, ppool));
}
 *)

(* JIEUNG: This one is only for checking, so we do not nneed this one? *)


(*  
static bool mm_ptable_identity_update(struct mm_ptable *t, paddr_t pa_begin,
                                      paddr_t pa_end, uint64_t attrs, int flags,
                                      struct mpool *ppool)
{
        if (!mm_ptable_identity_prepare(t, pa_begin, pa_end, attrs, flags,
                                        ppool)) {
                return false;
        }

        mm_ptable_identity_commit(t, pa_begin, pa_end, attrs, flags, ppool);

        return true;
}
*)

(* JIEUNG: I skipped mm_ptable_identity_commit call in here - that function is for checking *)
Definition mm_ptable_identity_update (t pa_begin pa_end attrs flags ppool : var) (prepare_v : var) :=
  prepare_v #= (Call "mm_ptable_identity_prepare" [CBR t ; CBV pa_begin ; CBV pa_end ; CBV attrs ; CBV flags ;
                                                  CBR ppool]) #;
            (#if (prepare_v == Vtrue)
              then Skip
              else Return Vfalse)
            #; Return true.



(* JIEUNG: This is the only one recursive call up to heare. So, we need a testing for this *) 
(*  
static void mm_dump_table_recursive(struct mm_page_table *table, uint8_t level,
                                    int max_level)
{
        uint64_t i;

        for (i = 0; i < MM_PTE_PER_PAGE; i++) {
                if (!arch_mm_pte_is_present(table->entries[i], level)) {
                        continue;
                }

                dlog("%*s%x: %x\n", 4 * (max_level - level), "", i,
                     table->entries[i]);

                if (arch_mm_pte_is_table(table->entries[i], level)) {
                        mm_dump_table_recursive(
                                mm_page_table_from_pa(arch_mm_table_from_pte(
                                        table->entries[i], level)),
                                level - 1, max_level);
                }
        }
}
*)

Definition mm_dump_table_recursive (table level max_level : var)
           (i entries entry_i arch_is_present arch_is_table level_1 page_from_pa next_level: var) :=
  i #= 0 #;
    #while (i <= MM_PTE_PER_PAGE - 1)
    do
      (entries #= (table #@ 0) #;
               entry_i #= (entries #@ i) #;
               arch_is_present #= (Call "arch_mm_pte_is_present" [CBV entry_i; CBV level]) #;
               (#if (arch_is_present == Vfalse)
                 then Skip
                 else
                   arch_is_table #= (Call "arch_mm_pte_is_table" [CBV entry_i; CBV level]) #;
                                 (#if (arch_is_table)
                                   then
                                     page_from_pa #= (Call "arch_mm_table_from_pte" [CBV entry_i ; CBV level]) #;
                                                  next_level #= (Minus level (Vnat 1)) #;
                                                  (Call "mm_dump_table_recursive" [CBV page_from_pa ;
                                                                                  CBV next_level ;
                                                                                  CBV max_level])
                                   else Skip) #;
                                 i #= (i + 1) 
      )).

                  
(*  
static void mm_ptable_dump(struct mm_ptable *t, int flags)
{
        struct mm_page_table *tables = mm_page_table_from_pa(t->root);
        uint8_t max_level = mm_max_level(flags);
        uint8_t root_table_count = mm_root_table_count(flags);
        uint8_t i;

        for (i = 0; i < root_table_count; ++i) {
                mm_dump_table_recursive(&tables[i], max_level, max_level);
        }
}
*)

Definition mm_ptable_dump (t flags: var) (root_v tables max_level root_count i table_i: var) :stmt := 
  root_v #= (t #@ 0) #;
         tables #= (Call "mm_page_table_from_pa" [CBV root_v]) #;
         max_level #= (Call "mm_max_level" [CBV flags]) #;
         root_count #= (Call "mm_root_table_count" [CBV flags]) #;
         i #=  0 #;
         #while (i <= root_count - 1)
         do (table_i #= (tables #@ i) #;
                     (Call "mm_dump_table_recursive" [CBV table_i ; CBV max_level ; CBV max_level]) #;
                     i #= (i + 1)
            ).
         

  
(*  
tatic pte_t mm_merge_table_pte(pte_t table_pte, uint8_t level,
                                struct mpool *ppool)
{
        struct mm_page_table *table;
        uint64_t block_attrs;
        uint64_t table_attrs;
        uint64_t combined_attrs;
        paddr_t block_address;

        table = mm_page_table_from_pa(arch_mm_table_from_pte(table_pte, level));

        if (!arch_mm_pte_is_present(table->entries[0], level - 1)) {
                /* Free the table and return an absent entry. */
                mpool_free(ppool, table);
                return arch_mm_absent_pte(level);
        }

        /* Might not be possible to merge the table into a single block. */
        if (!arch_mm_is_block_allowed(level)) {
                return table_pte;
        }

        /* Replace table with a single block, with equivalent attributes. */
        block_attrs = arch_mm_pte_attrs(table->entries[0], level - 1);
        table_attrs = arch_mm_pte_attrs(table_pte, level);
        combined_attrs =
                arch_mm_combine_table_entry_attrs(table_attrs, block_attrs);
        block_address = arch_mm_block_from_pte(table->entries[0], level - 1);

        /* Free the table and return a block. */
        mpool_free(ppool, table);
        return arch_mm_block_pte(level, block_address, combined_attrs);
}
 *)
            
Definition  mm_merge_table_pte (table_pte level ppool : var)
            (table block_attrs table_attrs combined_attrs block_address
                   arch_from_pte entries entry_0 arch_is_present arch_pte arch_is_allowed res: var) :=
  arch_from_pte #= (Call "arch_mm_table_from_pte" [CBR table_pte; CBV level]) #;
                table #= (Call "mm_page_table_from_pa" [CBV arch_from_pte]) #;
                entries #= (table #@ 0) #;
                entry_0 #= (entries #@ 0) #;
                arch_is_present #= (Call "arch_mm_pte_is_present" [CBV entry_0; CBV (level - 1)]) #;
                (#if (arch_is_present)
                  then Skip
                  else (Call "mpool_free" [CBR ppool; CBV table]) #;
                       arch_pte #= (Call "arch_mm_absent_pte" [CBV level]) #;
                       Return arch_pte
                ) #;
                arch_is_allowed #= (Call "arch_mm_is_block_allowed" [CBV level]) #;
                (#if (arch_is_allowed)
                  then Skip                         
                  else Return table_pte) #;
                (* Do it again for safety..?? *)
                entries #= (table #@ 0) #;
                entry_0 #= (entries #@ 0) #;
                block_attrs #= (Call "arch_mm_pte_attrs" [CBV entry_0; CBV (level - 1)]) #;
                table_attrs #= (Call "arch_mm_pte_attrs" [CBR table_pte; CBV level]) #;
                block_address #= (Call "arch_mm_block_from_pte" [CBV entry_0; CBV (level - 1)]) #;
                (Call "mpool_free" [CBV ppool; CBV table]) #;
                res #= (Call "arch_mm_block_pte" [CBV level; CBV block_address; CBV combined_attrs]) #;
                Return res.

(*
static pte_t mm_ptable_defrag_entry(pte_t entry, uint8_t level,
                                    struct mpool *ppool)
{
        struct mm_page_table *table;
        uint64_t i;
        bool mergeable;
        bool base_present;
        uint64_t base_attrs;

        if (!arch_mm_pte_is_table(entry, level)) {
                return entry;
        }

        table = mm_page_table_from_pa(arch_mm_table_from_pte(entry, level));

        static_assert(MM_PTE_PER_PAGE >= 1, "There must be at least one PTE.");
        table->entries[0] =
                mm_ptable_defrag_entry(table->entries[0], level - 1, ppool);
        base_present = arch_mm_pte_is_present(table->entries[0], level - 1);
        base_attrs = arch_mm_pte_attrs(table->entries[0], level - 1);

        mergeable = true;
        for (i = 1; i < MM_PTE_PER_PAGE; ++i) {
                bool present;

                table->entries[i] = mm_ptable_defrag_entry(table->entries[i],
                                                           level - 1, ppool);
                present = arch_mm_pte_is_present(table->entries[i], level - 1);

                if (present != base_present) {
                        mergeable = false;
                        continue;
                }

                if (!present) {
                        continue;
                }

                if (!arch_mm_pte_is_block(table->entries[i], level - 1)) {
                        mergeable = false;
                        continue;
                }

                if (arch_mm_pte_attrs(table->entries[i], level - 1) !=
                    base_attrs) {
                        mergeable = false;
                        continue;
                }
        }

        if (mergeable) {
                return mm_merge_table_pte(entry, level, ppool);
        }

        return entry;
}
 *)

Definition mm_ptable_defrag_entry (entry level ppool: var)
           (table i mergeable base_present base_attrs arch_is_table arch_from_pte
                  entry_0 entries entry_i mm_defrag_entry present arch_is_block arch_attrs res : var) :=
  arch_is_table #= (Call "arch_mm_pte_is_table" [CBV entry; CBV level]) #;
                (#if arch_is_table
                  then Skip
                  else Return entry) #;
                arch_from_pte #= (Call "arch_mm_table_from_pte" [CBV entry; CBV level]) #;
                table #= (Call "mm_page_table_from_pa" [CBV arch_from_pte]) #;
                entries #= (table #@ 0) #;
                entry_0 #= (entries #@ 0) #;
                entry_0 #= (Call "mm_ptable_defrag_entry" [CBV entry_0; CBV (level - 1); CBV ppool]) #;
                entries @ 0 #:= entry_0 #;
                table @ 0 #:= entries #;
                base_present #= (Call "arch_mm_pte_is_present" [CBV entry_0; CBV (level - 1)]) #;
                base_attrs #= (Call "arch_mm_pte_attrs" [CBV entry_0; CBV (level - 1)]) #;
                mergeable #= Vtrue #;
                
                i #= 1 #;
                
                (#while (i <= MM_PTE_PER_PAGE - 1)
                do (
                    entries #= (table #@ 0) #;
                            entry_i #= (entries #@ i) #;
                            entry_i #= (Call "mm_ptable_defrag_entry" [CBV entry_i; CBV (level - 1); CBV ppool]) #;
                            entries @ i #:= entry_i #;
                            table @ 0 #:= entries #;
                            
                            present #= (Call "arch_mm_pte_is_present" [CBV entry_i; CBV (level - 1)]) #;
                            (#if (present)
                              then
                                arch_is_block #= (Call "arch_mm_pte_is_block" [CBV entry_i; CBV (level - 1)]) #;
                                              (#if (arch_is_block)
                                                then
                                                  arch_attrs #= (Call "arch_mm_pte_attrs" [CBV entry_i;
                                                                                          CBV (level - 1)]) #;
                                                             (#if (arch_attrs == base_attrs)
                                                               then Skip
                                                               else mergeable #= false)
                                                else mergeable #= Vfalse)
                              else Skip) #;
                            i #= (i  + 1))) #;
                (#if (mergeable)
                  then res #= (Call "mm_merge_table_pte" [CBV entry; CBV level; CBV ppool]) #;
                           Return res
                  else Skip) #;
                Return entry.

(*
static bool mm_ptable_get_attrs_level(struct mm_page_table *table,
                                      ptable_addr_t begin, ptable_addr_t end,
                                      uint8_t level, bool got_attrs,
                                      uint64_t *attrs)
{
        pte_t *pte = &table->entries[mm_index(begin, level)];
        ptable_addr_t level_end = mm_level_end(begin, level);
        size_t entry_size = mm_entry_size(level);

        /* Cap end so that we don't go over the current level max. */
        if (end > level_end) {
                end = level_end;
        }

        /* Check that each entry is owned. */
        while (begin < end) {
                if (arch_mm_pte_is_table( *pte, level)) {
                        if (!mm_ptable_get_attrs_level(
                                    mm_page_table_from_pa(
                                            arch_mm_table_from_pte( *pte,
                                                                   level)),
                                    begin, end, level - 1, got_attrs, attrs)) {
                                return false;
                        }
                        got_attrs = true;
                } else {
                        if (!got_attrs) {
                                *attrs = arch_mm_pte_attrs( *pte, level);
                                got_attrs = true;
                        } else if (arch_mm_pte_attrs( *pte, level) != *attrs) {
                                return false;
                        }
                }

                begin = mm_start_of_next_block(begin, entry_size);
                pte++;
        }

        /* The entry is a valid block. */
        return got_attrs;
}
 *)

Definition mm_ptable_get_attrs_level (table begin_v end_v level got_attrs attrs : var)
           (mm_index_v entries entry_i pte level_end entry_size arch_is_table mm_attrs
                       arch_pte mm_from_pa arch_attrs mm_next_block: var) :=
  mm_index_v #= (Call "mm_index" [CBV begin_v; CBV level]) #;
             (* JIEUNG: Is it correct???? I need to confirm it *)
             entries #= (table #@ 0) #;
             entry_i #= (entries #@ mm_index_v) #;
             level_end #= (Call "mm_level_end" [CBV begin_v; CBV level]) #;
             entry_size #= (Call "mm_entry_size" [CBV level]) #;
             
             (#if (level_end <= end_v)
               then Skip
               else end_v #= level_end) #;
             
             #while (begin_v <= end_v - 1)
             do (arch_is_table #= (Call "arch_mm_pte_is_table" [CBV pte; CBV level]) #;
                               (#if (arch_is_table)
                                 then
                                   arch_pte #= (Call "arch_mm_table_from_pte" [CBV pte; CBV level]) #;
                                            mm_from_pa #= (Call "mm_page_table_from_pa" [CBV arch_pte]) #;
                                            mm_attrs #= (Call "mm_ptable_get_attrs_level" [CBV mm_from_pa;
                                                                                          CBV begin_v; CBV end_v;
                                                                                          CBV (level - 1) ;
                                                                                          CBV got_attrs; CBV attrs]) #;
                                            (#if mm_attrs
                                              then Skip
                                              else Return Vfalse) #;
                                            got_attrs #= Vtrue 
                                 else
                                   (#if got_attrs
                                     then
                                       arch_attrs #= (Call "arch_mm_pte_attrs" [CBV pte; CBV level]) #;
                                                  (#if (arch_attrs == attrs)
                                                    then Skip
                                                    else Return Vfalse)
                                     else
                                       attrs #= (Call "arch_mm_pte_attrs" [CBV pte; CBV level]) #;
                                             got_attrs #= Vtrue
                                   )
                               ) #;
                               begin_v #= (Call "mm_start_of_next_block" [CBV begin_v; CBV entry_size]) #;
                               pte #= (pte + 1)
                ) #;
                  Return got_attrs.

(*  
static bool mm_vm_get_attrs(struct mm_ptable *t, ptable_addr_t begin,
                            ptable_addr_t end, uint64_t *attrs)
{
        int flags = 0;
        uint8_t max_level = mm_max_level(flags);
        uint8_t root_level = max_level + 1;
        size_t root_table_size = mm_entry_size(root_level);
        ptable_addr_t ptable_end =
                mm_root_table_count(flags) * mm_entry_size(root_level);
        struct mm_page_table *table;
        bool got_attrs = false;

        begin = mm_round_down_to_page(begin);
        end = mm_round_up_to_page(end);

        /* Fail if the addresses are out of range. */
        if (end > ptable_end) {
                return false;
        }

        table = &mm_page_table_from_pa(t->root)[mm_index(begin, root_level)];
        while (begin < end) {
                if (!mm_ptable_get_attrs_level(table, begin, end, max_level,
                                               got_attrs, attrs)) {
                        return false;
                }

                got_attrs = true;
                begin = mm_start_of_next_block(begin, root_table_size);
                table++;
        }

        return got_attrs;
}
*)

(* JIEUNG: again, when do we have to use CBR and when do we have to use CBV? *)
Definition mm_vm_get_attrs (t begin_v end_v attrs: var)
           (flags max_level root_level root_table_size 
                  ptable_end root_count entry_size table got_attrs root_v mm_index_v
                  pt_from_pa mm_attrs_level : var) :=
  flags #= 0 #;
        max_level #= (Call "mm_max_level" [CBV flags]) #;
        root_level #= (max_level + 1) #;
        root_table_size #= (Call "mm_entry_size" [CBV root_level]) #;
        root_count #= (Call "mm_root_table_count" [CBV flags]) #;
        entry_size #= (Call "mm_entry_size" [CBV root_level]) #;
        ptable_end #= (root_count * entry_size) #;
        got_attrs #= Vfalse #;
        begin_v #= (Call "mm_round_down_to_page" [CBV begin_v]) #;
        end_v #= (Call "mm_round_up_to_page" [CBV end_v]) #;
        
        (#if (ptable_end <= end_v)
          then Skip
          else Return Vfalse) #;
        
        (* JIEUNG: I am not sure whether the following part is correct or not *)
        root_v #= (t #@ 0) #;
        pt_from_pa #= (Call "mm_page_table_from_pa" [CBV root_v]) #;
        mm_index_v #= (Call "mm_index" [CBV begin_v; CBV root_level]) #;
        table #= (pt_from_pa #@ mm_index_v) #;
        
        (#while (begin_v <= end_v - 1)
          do (mm_attrs_level #= (Call "mm_ptable_get_attrs_level" [CBR table; CBV begin_v; CBV end_v; CBV max_level;
                                                                  CBV got_attrs; CBV attrs]) #;
                             (#if (mm_attrs_level)
                               then Skip
                               else Return Vfalse) #;
                             got_attrs #= Vtrue #;
                             begin_v #= (Call "mm_start_of_next_block" [CBV begin_v; CBV root_table_size]) #;
                             table #= (table + 1))) #;
        Return got_attrs.

(*
bool mm_vm_init(struct mm_ptable *t, struct mpool *ppool)
{
        return mm_ptable_init(t, 0, ppool);
}
*)


Definition mm_vm_init (t ppool : var) (init_v : var) :=
  init_v #= (Call "mm_ptable_init" [CBV t; CBV (Vnat 0); CBR ppool]) #;
         Return init_v.

  
(*
void mm_vm_fini(struct mm_ptable *t, struct mpool *ppool)
{    
        mm_ptable_fini(t, 0, ppool);
}
 *)

Definition mm_vm_fini (t ppool : var) :=
  (Call "mm_ptable_fini" [CBV t; CBV (Vnat 0) ; CBR ppool]).


(*  
static int mm_mode_to_flags(uint32_t mode)
{
        if ((mode & MM_MODE_UNMAPPED_MASK) == MM_MODE_UNMAPPED_MASK) {
                return MM_FLAG_UNMAP;
        }

        return 0;
}
 *)

Definition mm_mode_to_flags (mode : var) :=
  #if ((And mode MM_MODE_UNMAPPED_MASK) == MM_MODE_UNMAPPED_MASK)
   then Return MM_FLAG_UNMAP
   else Return (Vnat 0).


(*
bool mm_vm_identity_prepare(struct mm_ptable *t, paddr_t begin, paddr_t end,
                            uint32_t mode, struct mpool *ppool)
{
        int flags = mm_mode_to_flags(mode);

        return mm_ptable_identity_prepare(t, begin, end,
                                          arch_mm_mode_to_stage2_attrs(mode),
                                          flags, ppool);
}
 *)

Definition mm_vm_identity_prepare (t begin_v end_v mode ppool : var) (flags arch_attrs res : var) :=
  flags #= (Call "mm_mode_to_flags" [CBV mode]) #;
        arch_attrs #= (Call "arch_mm_mode_to_sage2_attrs" [CBV mode]) #;
        res #= (Call "mm_ptable_identity_prepare" [CBR t; CBV begin_v; CBV end_v; CBV arch_attrs; CBV flags; CBR ppool]) #;
        Return res.
                                                  

(*
void mm_vm_identity_commit(struct mm_ptable *t, paddr_t begin, paddr_t end,
                           uint32_t mode, struct mpool *ppool, ipaddr_t *ipa)
{
        int flags = mm_mode_to_flags(mode);

        mm_ptable_identity_commit(t, begin, end,
                                  arch_mm_mode_to_stage2_attrs(mode), flags,
                                  ppool);

        if (ipa != NULL) {
                *ipa = ipa_from_pa(begin);
        }
}
 *)

Definition mm_vm_identity_commit (t begin_v end_v mode ppool ipa: var) (flags arch_attrs : var) :=
  flags #= (Call "mm_mode_to_flags" [CBV mode]) #;
        arch_attrs #= (Call "arch_mm_mode_to_sage2_attrs" [CBV mode]) #;
        (Call "mm_ptable_identity_commit" [CBR t; CBV begin_v; CBV end_v; CBV arch_attrs; CBV flags; CBR ppool]) #;
        #if (ipa == Vnull)
         then Skip
         else ipa #= (Call "ipa_from_pa" [CBV begin_v]).

(*
bool mm_vm_identity_map(struct mm_ptable *t, paddr_t begin, paddr_t end,
                        uint32_t mode, struct mpool *ppool, ipaddr_t *ipa)
{
        int flags = mm_mode_to_flags(mode);
        bool success = mm_ptable_identity_update(
                t, begin, end, arch_mm_mode_to_stage2_attrs(mode), flags,
                ppool);

        if (success && ipa != NULL) {
                *ipa = ipa_from_pa(begin);
        }

        return success;
}
 *)

Definition mm_vm_identity_map (t begin_v end_v mode ppool ipa: var) (flags success arch_attrs : var) :=
  flags #= (Call "mm_mode_to_flags" [CBV mode]) #;
        arch_attrs #= (Call "arch_mm_mode_to_sage2_attrs" [CBV mode]) #;
        success #= (Call "mm_ptable_identity_update" [CBR t ; CBV begin_v ; CBV end_v ; CBV arch_attrs ;
                                                     CBV flags ; CBR ppool]) #;
        (#if (success)
          then (#if (ipa == Vnull)
                 then Skip
                 else ipa #= (Call "ipa_from_pa" [CBV begin_v]))
          else Skip) #;
        Return success.


(*  
bool mm_vm_unmap(struct mm_ptable *t, paddr_t begin, paddr_t end,
                 struct mpool *ppool)
{
        uint32_t mode = MM_MODE_UNMAPPED_MASK;

        return mm_vm_identity_map(t, begin, end, mode, ppool, NULL);
}
 *)

Definition mm_vm_unmap (t begin_v end_v ppool : var) (mode res: var) :=
  mode #= MM_MODE_UNMAPPED_MASK #;
       res #= (Call "mm_vm_identity_map" [CBR t ; CBV begin_v ; CBV end_v ; CBV mode ; CBR ppool ; CBV Vnull]).

(*  
void mm_vm_dump(struct mm_ptable *t)
{
        mm_ptable_dump(t, 0);
}
 *)
Definition mm_vm_dump (t : var) :=
  (Call "mm_ptable_dump" [CBR t; CBV (Vnat 0)]).
  
(*
void mm_vm_defrag(struct mm_ptable *t, struct mpool *ppool)
{
        mm_ptable_defrag(t, 0, ppool);
}
*)
Definition mm_vm_defrag (t ppool : var) :=
  (Call "mm_ptable_defrag" [CBR t; CBV (Vnat 0); CBR ppool]).

(*
bool mm_vm_get_mode(struct mm_ptable *t, ipaddr_t begin, ipaddr_t end,
                    uint32_t *mode)
{
        uint64_t attrs;
        bool ret;

        ret = mm_vm_get_attrs(t, ipa_addr(begin), ipa_addr(end), &attrs);
        if (ret) {
                *mode = arch_mm_stage2_attrs_to_mode(attrs);
        }

        return ret;
}
 *)

Definition mm_vm_get_mode (t begin_v end_v mode: var) (attrs ret  ipa_addr_b_v ipa_addr_e_v : var) : stmt :=
  ipa_addr_b_v #= (Call "ipa_addr" [CBV begin_v]) #;
               ipa_addr_e_v #= (Call "ipa_addr" [CBV end_v]) #;
               ret #= (Call "mm_vm_get_attrs" [CBR t ; CBV ipa_addr_b_v ; CBV ipa_addr_e_v ; CBR attrs]) #;
               (#if (ret)
                 then mode #= (Call "arch_mm_stage2_attrs_to_mode" [CBV attrs])
                 else Skip) #;
               Return ret.

(* JIEUNG: I hope to check this function with YJ  *)
(*
static struct mm_stage1_locked mm_stage1_lock_unsafe(void)
{
        return (struct mm_stage1_locked){.ptable = &ptable};
}
 *) 

(*
struct mm_stage1_locked mm_lock_stage1(void)
{
        sl_lock(&ptable_lock);
        return mm_stage1_lock_unsafe();
}
*)

(* JIEUNG: I need to change the following two things with interaction tree style lock operations *)
Definition mm_lock_stage1 (res : var) :=
  (Call "sl_lock" [CBV ptable_lock]) #;
                                     res #= (Call "mm_stage1_lock_unsafe" []) #;
                                     Return res.

(*
void mm_unlock_stage1(struct mm_stage1_locked *lock)
{
        CHECK(lock->ptable == &ptable);
        sl_unlock(&ptable_lock);
        lock->ptable = NULL;
}
 *)

Definition mm_unlock_stage1 (lock: var) :=
  (Call "sl_unlock" [CBV ptable_lock]) #; lock @ 0 #:= Vnull.

(*
void *mm_identity_map(struct mm_stage1_locked stage1_locked, paddr_t begin,
                      paddr_t end, uint32_t mode, struct mpool *ppool)
{
        int flags = MM_FLAG_STAGE1 | mm_mode_to_flags(mode);

        if (mm_ptable_identity_update(stage1_locked.ptable, begin, end,
                                      arch_mm_mode_to_stage1_attrs(mode), flags,
                                      ppool)) {
                return ptr_from_va(va_from_pa(begin));
        }

        return NULL;
}
 *)

Definition mm_identity_map (stage1_locked begin_v end_v mode ppool : var) (flags_res flags attrs_res cond_res res : var) :=
  flags_res #= (Call "mm_mode_to_flags" [CBV mode]) #;
            flags #= Or MM_FLAG_STAGE1 flags_res #;
            attrs_res #= (Call "arch_mm_mode_to_stage1_attrs" [CBV mode]) #;
            cond_res #= (Call "mm_ptable_identity_update" [CBR stage1_locked; CBV begin_v; CBV end_v;
                                                          CBV attrs_res; CBV flags; CBR ppool]) #;
            #if cond_res
             then res #= (Call "ptr_from_va" [CBV begin_v])
             else Vnull.

            
(*
bool mm_unmap(struct mm_stage1_locked stage1_locked, paddr_t begin, paddr_t end,
              struct mpool *ppool)
{
        uint32_t mode = MM_MODE_UNMAPPED_MASK;

        return mm_identity_map(stage1_locked, begin, end, mode, ppool);
}
*)


Definition mm_unmap (stage1_locked begin_v end_v ppool : var) (mode : var) : stmt :=
  mode #= MM_MODE_UNMAPPED_MASK #;
       (Call "mm_identity_map" [CBR stage1_locked ; CBV begin_v ; CBV end_v ; CBV mode ; CBR ppool]).

(*
void mm_defrag(struct mm_stage1_locked stage1_locked, struct mpool *ppool)
{
        mm_ptable_defrag(stage1_locked.ptable, MM_FLAG_STAGE1, ppool);
}
 *)

Definition mm_defrag (stage1_locked ppool : var) (arg1 : var) : stmt :=
  arg1 #= (stage1_locked #@ 0) #;
       (Call "mm_ptable_defrag" [CBV arg1 ; CBR ppool]).

(*
bool mm_init(struct mpool *ppool)
{
        /* Locking is not enabled yet so fake it, */
        struct mm_stage1_locked stage1_locked = mm_stage1_lock_unsafe();



        if (!mm_ptable_init(&ptable, MM_FLAG_STAGE1, ppool)) {
                dlog_error("Unable to allocate memory for page table.\n");
                return false;
        }

        /* Let console driver map pages for itself. */
        plat_console_mm_init(stage1_locked, ppool);

        /* Map each section. */
        mm_identity_map(stage1_locked, layout_text_begin(), layout_text_end(),
                        MM_MODE_X, ppool);

        mm_identity_map(stage1_locked, layout_rodata_begin(),
                        layout_rodata_end(), MM_MODE_R, ppool);

        mm_identity_map(stage1_locked, layout_data_begin(), layout_data_end(),
                        MM_MODE_R | MM_MODE_W, ppool);

        return arch_mm_init(ptable.root);
}
 *)


(* ptable is defined in mm.h file *)
Definition ptable := "ptable".

(* JIEUNG: where is the ptable declaration? I need to move that one. 
   And, where is lock initialization? *)
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

End MM.

