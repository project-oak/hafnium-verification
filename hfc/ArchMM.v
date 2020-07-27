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


Require Import Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.
Require Import BitNat.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Local Open Scope N_scope.


Module ArchMM.

  (*

/* Keep macro alignment */
/* clang-format off */

#define NON_SHAREABLE   UINT64_C(0)
#define OUTER_SHAREABLE UINT64_C(2)
#define INNER_SHAREABLE UINT64_C(3)

#define PTE_VALID        (UINT64_C(1) << 0)
#define PTE_LEVEL0_BLOCK (UINT64_C(1) << 1)
#define PTE_TABLE        (UINT64_C(1) << 1)

#define STAGE1_XN          (UINT64_C(1) << 54)
#define STAGE1_PXN         (UINT64_C(1) << 53)
#define STAGE1_CONTIGUOUS  (UINT64_C(1) << 52)
#define STAGE1_DBM         (UINT64_C(1) << 51)
#define STAGE1_NG          (UINT64_C(1) << 11)
#define STAGE1_AF          (UINT64_C(1) << 10)
#define STAGE1_SH(x)       ((x) << 8)
#define STAGE1_AP2         (UINT64_C(1) << 7)
#define STAGE1_AP1         (UINT64_C(1) << 6)
#define STAGE1_AP(x)       ((x) << 6)
#define STAGE1_NS          (UINT64_C(1) << 5)
#define STAGE1_ATTRINDX(x) ((x) << 2)

#define STAGE1_READONLY  UINT64_C(2)
#define STAGE1_READWRITE UINT64_C(0)

#define STAGE1_DEVICEINDX UINT64_C(0)
#define STAGE1_NORMALINDX UINT64_C(1)

#define STAGE2_XN(x)      ((x) << 53)
#define STAGE2_CONTIGUOUS (UINT64_C(1) << 52)
#define STAGE2_DBM        (UINT64_C(1) << 51)
#define STAGE2_AF         (UINT64_C(1) << 10)
#define STAGE2_SH(x)      ((x) << 8)
#define STAGE2_S2AP(x)    ((x) << 6)

#define STAGE2_EXECUTE_ALL  UINT64_C(0)
#define STAGE2_EXECUTE_EL0  UINT64_C(1)
#define STAGE2_EXECUTE_NONE UINT64_C(2)
#define STAGE2_EXECUTE_EL1  UINT64_C(3)
#define STAGE2_EXECUTE_MASK UINT64_C(3)


/* Table attributes only apply to stage 1 translations. */
#define TABLE_NSTABLE  (UINT64_C(1) << 63)
#define TABLE_APTABLE1 (UINT64_C(1) << 62)
#define TABLE_APTABLE0 (UINT64_C(1) << 61)
#define TABLE_XNTABLE  (UINT64_C(1) << 60)
#define TABLE_PXNTABLE (UINT64_C(1) << 59)

/* The following are stage-2 software defined attributes. */
#define STAGE2_SW_OWNED     (UINT64_C(1) << 55)
#define STAGE2_SW_EXCLUSIVE (UINT64_C(1) << 56)


/* The following are stage-2 memory attributes for normal memory. */
#define STAGE2_DEVICE_MEMORY UINT64_C(0)
#define STAGE2_NONCACHEABLE  UINT64_C(1)
#define STAGE2_WRITETHROUGH  UINT64_C(2)
#define STAGE2_WRITEBACK     UINT64_C(3)

/* The following are stage-2 memory attributes for device memory. */
#define STAGE2_MEMATTR_DEVICE_nGnRnE UINT64_C(0)
#define STAGE2_MEMATTR_DEVICE_nGnRE  UINT64_C(1)
#define STAGE2_MEMATTR_DEVICE_nGRE   UINT64_C(2)
#define STAGE2_MEMATTR_DEVICE_GRE    UINT64_C(3)

/* The following construct and destruct stage-2 memory attributes. */
#define STAGE2_MEMATTR(outer, inner) ((((outer) << 2) | (inner)) << 2)
#define STAGE2_MEMATTR_TYPE_MASK UINT64_C(3 << 4)

#define STAGE2_ACCESS_READ  UINT64_C(1)
#define STAGE2_ACCESS_WRITE UINT64_C(2)

#define CACHE_WORD_SIZE 4

/**
 * Threshold number of pages in TLB to invalidate after which we invalidate all
 * TLB entries on a given level.
 * Constant is the number of pointers per page table entry, also used by Linux.
 */
#define MAX_TLBI_OPS  MM_PTE_PER_PAGE

/* clang-format on */


   *)


  
  (*


/**
 * Threshold number of pages in TLB to invalidate after which we invalidate all
 * TLB entries on a given level.
 * Constant is the number of pointers per page table entry, also used by Linux.
 */
#define MAX_TLBI_OPS  MM_PTE_PER_PAGE

/* clang-format on */

#define tlbi(op)                               \
    do {                                   \
        __asm__ volatile("tlbi " #op); \
    } while (0)
#define tlbi_reg(op, reg)                                              \
    do {                                                           \
        __asm__ __volatile__("tlbi " #op ", %0" : : "r"(reg)); \
    } while (0)

/** Mask for the address bits of the pte. */
#define PTE_ADDR_MASK \
    (((UINT64_C(1) << 48) - 1) & ~((UINT64_C(1) << PAGE_BITS) - 1))

/** Mask for the attribute bits of the pte. */
#define PTE_ATTR_MASK (~(PTE_ADDR_MASK | (UINT64_C(1) << 1)))

/**
 * Configuration information for memory management. Order is important as this
 * is read from assembly.
 *
 * It must only be written to from `arch_mm_init()` to avoid cache and
 * synchronization problems.
 */
struct arch_mm_config {
    uintreg_t ttbr0_el2;
    uintreg_t vtcr_el2;
    uintreg_t mair_el2;
    uintreg_t tcr_el2;
    uintreg_t sctlr_el2;
} arch_mm_config;

static uint8_t mm_s2_max_level;
static uint8_t mm_s2_root_table_count;

   *)

  Definition mm_s2_max_level : var := "mm_s2_max_level".
  Definition mm_s2_root_table_count : var := " mm_s2_root_table_count".

  Definition UINT64_C_1 := UINT64_C 1.

  Definition PTE_ADDR_MASK :=
    (BAnd (Minus (ShiftL UINT64_C_1 48) 1) (BNot (Minus (ShiftL UINT64_C_1 PAGE_BITS) 1))).
  Definition PTE_ATTR_MASK :=
    (BNot (BOr PTE_ADDR_MASK (ShiftL UINT64_C_1 1))). 

  Definition MAX_TLBI_OPS := MM_PTE_PER_PAGE.

  Definition CACHE_WORD_SIZE :expr := 4.
  Definition UINT16_C (val : expr) := val.
  Definition UINT16_C_1 := UINT16_C 1.

  Definition NON_SHAREABLE := UINT64_C 0.
  Definition OUTER_SHAREABLE := UINT64_C 2.
  Definition INNER_SHAREABLE := UINT64_C 3.

  Definition PTE_VALID := ShiftL UINT64_C_1 0.
  Definition PTE_LEVEL0_BLOCK := ShiftL UINT64_C_1 1.
  Definition PTE_TABLE := ShiftL UINT64_C_1 1.

  Definition STAGE2_SW_OWNED := ShiftL UINT64_C_1 55.
  Definition STAGE2_SW_EXCLUSIVE := ShiftL UINT64_C_1 56.

  Definition STAGE1_XN := ShiftL UINT64_C_1 54.
  Definition STAGE1_PXN := ShiftL UINT64_C_1 53.
  Definition STAGE1_CONTIGUOUS := ShiftL UINT64_C_1 52.
  Definition STAGE1_DBM := ShiftL UINT64_C_1 51.
  Definition STAGE1_NG := ShiftL UINT64_C_1 11.
  Definition STAGE1_AF := ShiftL UINT64_C_1 10.
  Definition STAGE1_SH := fun x => ShiftL x 8.
  Definition STAGE1_AP2 := ShiftL UINT64_C_1 7.
  Definition STAGE1_AP1 := ShiftL UINT64_C_1 6.
  Definition STAGE1_AP := fun x => ShiftL x 6.
  Definition STAGE1_NS := ShiftL UINT64_C_1 5.
  Definition STAGE1_ATTRINDX := fun x => ShiftL x 2.

  Definition STAGE1_READONLY := UINT64_C 2.
  Definition STAGE1_READWRITE := UINT64_C 0.

  Definition STAGE1_DEVICEINDX := UINT64_C 0.
  Definition STAGE1_NORMALINDX := UINT64_C 1.

  Definition STAGE2_XN := fun x => ShiftL x 53.
  Definition STAGE2_CONTIGUOUS := ShiftL UINT64_C_1 52.
  Definition STAGE2_DBM := ShiftL UINT64_C_1 51.
  Definition STAGE2_AF := ShiftL UINT64_C_1 10.
  Definition STAGE2_SH := fun x => ShiftL x 8.
  Definition STAGE2_S2AP := fun x => ShiftL x 6.

  Definition STAGE2_EXECUTE_ALL := UINT64_C 0.
  Definition STAGE2_EXECUTE_EL0 := UINT64_C 1.
  Definition STAGE2_EXECUTE_NONE := UINT64_C 2.
  Definition STAGE2_EXECUTE_EL1 := UINT64_C 3.
  Definition STAGE2_EXECUTE_MASK := UINT64_C 3.

  Definition STAGE2_ACCESS_READ := UINT64_C 1.
  Definition STAGE2_ACCESS_WRITE := UINT64_C 2.

  Definition STAGE2_DEVICE_MEMORY := UINT64_C 0.
  Definition STAGE2_NONCACHEABLE := UINT64_C 1.
  Definition STAGE2_WRITETHROUGH := UINT64_C 2.
  Definition STAGE2_WRITEBACK := UINT64_C 3.

  Definition STAGE2_MEMATTR_DEVICE_nGnRnE := UINT64_C 0.
  Definition STAGE2_MEMATTR_DEVICE_nGnRE := UINT64_C 1.
  Definition STAGE2_MEMATTR_DEVICE_nGRE := UINT64_C 2.
  Definition STAGE2_MEMATTR_DEVICE_GRE := UINT64_C 3.

  Definition STAGE2_MEMATTR (outer inner: expr) := (Or (ShiftL outer 2) (ShiftL inner 2)).
  Definition STAGE2_MEMATTR_TYPE_MASK := UINT64_C (N.shiftl 3 4).

  Definition TABLE_NSTABLE := ShiftL UINT64_C_1 63.
  Definition TABLE_APTABLE1 := ShiftL UINT64_C_1 62.
  Definition TABLE_APTABLE0 := ShiftL UINT64_C_1 61.
  Definition TABLE_XNTABLE := ShiftL UINT64_C_1 60.
  Definition TABLE_PXNTABLE := ShiftL UINT64_C_1 59.

  (* /** Mask for the address bits of the pte. */ *)
  (* #define PTE_ADDR_MASK \ *)
  (*     (((UINT64_C(1) << 48) - 1) & ~((UINT64_C(1) << PAGE_BITS) - 1)) *)

  (*
/**
 * Returns the encoding of a page table entry that isn't present.
 */
pte_t arch_mm_absent_pte(uint8_t level)
{
    (void)level;
    return 0;
}

   *)

  Definition arch_mm_absent_pte (level:var) : stmt := Return 0.

  (*
/**
 * Converts a physical address to a table PTE.
 *
 * The spec says that 'Table descriptors for stage 2 translations do not
 * include any attribute field', so we don't take any attributes as arguments.
 */
pte_t arch_mm_table_pte(uint8_t level, paddr_t pa)
{
    /* This is the same for all levels on aarch64. */
    (void)level;
    return pa_addr(pa) | PTE_TABLE | PTE_VALID;
}
   *)

  Definition arch_mm_table_pte (level pa:var)
             (pa_addr_res pte_table_res res :var) : stmt :=
    (* (void)level; : just Compiler warning suppress *)
    pa_addr_res #= (Call "pa_addr" [CBV pa]) #;
                pte_table_res #= pa_addr_res #| PTE_TABLE #;
                res #= pte_table_res #| PTE_VALID #;
                Return res.

  (*

/**
 * Converts a physical address to a block PTE.
 *
 * The level must allow block entries.
 */
pte_t arch_mm_block_pte(uint8_t level, paddr_t pa, uint64_t attrs)
{
    pte_t pte = pa_addr(pa) | attrs;

    if (level == 0) {
        /* A level 0 'block' is actually a page entry. */
        pte |= PTE_LEVEL0_BLOCK;
    }
    return pte;
}

   *)

  Definition arch_mm_block_pte (level pa attrs:var) (pa_addr_res pte:var) :=
    pa_addr_res #= (Call "pa_addr" [CBV pa]) #;
                pte #= pa_addr_res #| attrs #;
                (#if (level == 0)
                  then pte #= pte #| PTE_LEVEL0_BLOCK
                  else Skip) #;
                Return pte.


  (*
/**
 * Specifies whether block mappings are acceptable at the given level.
 *
 * Level 0 must allow block entries.
 */
bool arch_mm_is_block_allowed(uint8_t level)
{
    return level <= 2;
}

   *)

  Definition arch_mm_is_block_allowed (level:var) :=
    Return (level <= 2).

  (*
/**
 * Determines if the given pte is present, i.e., if it is valid or it is invalid
 * but still holds state about the memory so needs to be present in the table.
 */
bool arch_mm_pte_is_present(pte_t pte, uint8_t level)
{
    return arch_mm_pte_is_valid(pte, level) || (pte & STAGE2_SW_OWNED) != 0;
}

   *)

  Definition arch_mm_pte_is_present (pte level:var) (pte_valid sw_owned res:var) :=
    pte_valid #= (Call "arch_mm_pte_is_valid" [CBV pte; CBV level]) #;
              sw_owned #= BAnd pte STAGE2_SW_OWNED #;
              res #= pte_valid #|| sw_owned #;
              #if (res == 0)
               then Return Vfalse
               else Return Vtrue.

  (*
/**
 * Determines if the given pte is valid, i.e., if it points to another table,
 * to a page, or a block of pages that can be accessed.
 */
bool arch_mm_pte_is_valid(pte_t pte, uint8_t level)
{
    (void)level;
    return (pte & PTE_VALID) != 0;
}

   *)

  Definition arch_mm_pte_is_valid (pte level:var) (pte_valid:var) :=
    pte_valid #= BAnd pte PTE_VALID #;
              #if (pte_valid == 0)
               then Return Vfalse
               else Return Vtrue.

  (*
/**
 * Determines if the given pte references a block of pages.
 */
bool arch_mm_pte_is_block(pte_t pte, uint8_t level)
{
    /* We count pages at level 0 as blocks. */
    return arch_mm_is_block_allowed(level) &&
           (level == 0 ? (pte & PTE_LEVEL0_BLOCK) != 0
               : arch_mm_pte_is_present(pte, level) &&
                     !arch_mm_pte_is_table(pte, level));
}

   *)

  Definition arch_mm_pte_is_block (pte level:var) (blk_allowed ret is_blk is_present is_table:var) :=
    blk_allowed #= (Call "arch_mm_is_block_allowed" [CBV level]) #;
                (#if (level == 0)
                  then (#if (pte #& PTE_LEVEL0_BLOCK)
                         then (ret #= Val Vfalse)
                         else (ret #= Val Vtrue))
                  else (is_present #= (Call "arch_mm_pte_is_present" [CBV pte; CBV level]) #;
                                   is_table #= (Call "arch_mm_pte_is_present" [CBV pte; CBV level]) #;
                                   ret #= (is_present #&& (#! is_table)))) #;
                Return (blk_allowed #&& ret).

  (*
/**
 * Determines if the given pte references another table.
 */
bool arch_mm_pte_is_table(pte_t pte, uint8_t level)
{
    return level != 0 && arch_mm_pte_is_valid(pte, level) &&
           (pte & PTE_TABLE) != 0;
}

   *)

  Definition arch_mm_pte_is_table (pte level:var) (is_valid :var) :=
    is_valid #= (Call "arch_mm_pte_is_valid" [CBV pte; CBV level]) #;
             Return ((#! (level == 0)) #&& is_valid #&& (#! (pte #& PTE_TABLE) == 0)).
  
  (*
static uint64_t pte_addr(pte_t pte)
{
    return pte & PTE_ADDR_MASK;
}

   *)

  Definition pte_addr (pte:var) :=
    Return (pte #& PTE_ADDR_MASK).

  (*
/**
 * Clears the given physical address, i.e., clears the bits of the address that
 * are not used in the pte.
 */
paddr_t arch_mm_clear_pa(paddr_t pa)
{
    return pa_init(pte_addr(pa_addr(pa)));
}

   *)

  Definition arch_mm_clear_pa (pa:var) (addr1 addr2 res:var) :=
    addr1 #= (Call "pa_addr" [CBV pa]) #;
          addr2 #= (Call "pte_addr" [CBV addr1]) #;
          res #= (Call "pa_init" [CBV addr2]) #;
          Return res.

  (*
/**
 * Extracts the physical address of the block referred to by the given page
 * table entry.
 */
paddr_t arch_mm_block_from_pte(pte_t pte, uint8_t level)
{
    (void)level;
    return pa_init(pte_addr(pte));
}

   *)

  Definition arch_mm_block_from_pte (pte level:var) (addr res:var) :=
    addr #= (Call "pte_addr" [CBV pte]) #;
         res #= (Call "pa_init" [CBV addr]) #;
         Return res.

  (*
/**
 * Extracts the physical address of the page table referred to by the given page
 * table entry.
 */
paddr_t arch_mm_table_from_pte(pte_t pte, uint8_t level)
{
    (void)level;
    return pa_init(pte_addr(pte));
}

   *)

  Definition arch_mm_table_from_pte (pte level:var) (addr res:var) :=
    addr #= (Call "pte_addr" [CBV pte]) #;
         res #= (Call "pa_init" [CBV addr]) #;
         Return res.

  (*
/**
 * Extracts the architecture-specific attributes applies to the given page table
 * entry.
 */
uint64_t arch_mm_pte_attrs(pte_t pte, uint8_t level)
{
    (void)level;
    return pte & PTE_ATTR_MASK;
}

   *)
  Definition arch_mm_pte_attrs (pte level:var) :=
    Return (pte #& PTE_ATTR_MASK).

  (*
/**
 * Invalidates stage-1 TLB entries referring to the given virtual address range.
 */
void arch_mm_invalidate_stage1_range(vaddr_t va_begin, vaddr_t va_end)
{
    uintvaddr_t begin = va_addr(va_begin);
    uintvaddr_t end = va_addr(va_end);
    uintvaddr_t it;

    /* Sync with page table updates. */
    dsb(ishst);

    /*
     * Revisions prior to Armv8.4 do not support invalidating a range of
     * addresses, which means we have to loop over individual pages. If
     * there are too many, it is quicker to invalidate all TLB entries.
     */
    if ((end - begin) > (MAX_TLBI_OPS * PAGE_SIZE)) {
        if (VM_TOOLCHAIN == 1) {
            tlbi(vmalle1is);
        } else {
            tlbi(alle2is);
        }
    } else {
        begin >>= 12;
        end >>= 12;
        /* Invalidate stage-1 TLB, one page from the range at a time. */
        for (it = begin; it < end;
             it += (UINT64_C(1) << (PAGE_BITS - 12))) {
            if (VM_TOOLCHAIN == 1) {
                tlbi_reg(vae1is, it);
            } else {
                tlbi_reg(vae2is, it);
            }
        }
    }

    /* Sync data accesses with TLB invalidation completion. */
    dsb(ish);

    /* Sync instruction fetches with TLB invalidation completion. */
    isb();
}

   *)

  Definition arch_mm_invalidate_stage1_range (va_begin va_end:var) (begin_v end_v:var) :=
    begin_v #= (Call "va_addr" [CBV va_begin]) #;
            end_v #= (Call "va_addr" [CBV va_end]).

  (*
/**
 * Invalidates stage-2 TLB entries referring to the given intermediate physical
 * address range.
 */
void arch_mm_invalidate_stage2_range(ipaddr_t va_begin, ipaddr_t va_end)
{
    uintpaddr_t begin = ipa_addr(va_begin);
    uintpaddr_t end = ipa_addr(va_end);
    uintpaddr_t it;

    /* TODO: This only applies to the current VMID. */

    /* Sync with page table updates. */
    dsb(ishst);

    /*
     * Revisions prior to Armv8.4 do not support invalidating a range of
     * addresses, which means we have to loop over individual pages. If
     * there are too many, it is quicker to invalidate all TLB entries.
     */
    if ((end - begin) > (MAX_TLBI_OPS * PAGE_SIZE)) {
        /*
         * Invalidate all stage-1 and stage-2 entries of the TLB for
         * the current VMID.
         */
        tlbi(vmalls12e1is);
    } else {
        begin >>= 12;
        end >>= 12;

        /*
         * Invalidate stage-2 TLB, one page from the range at a time.
         * Note that this has no effect if the CPU has a TLB with
         * combined stage-1/stage-2 translation.
         */
        for (it = begin; it < end;
             it += (UINT64_C(1) << (PAGE_BITS - 12))) {
            tlbi_reg(ipas2e1is, it);
        }

        /*
         * Ensure completion of stage-2 invalidation in case a page
         * table walk on another CPU refilled the TLB with a complete
         * stage-1 + stage-2 walk based on the old stage-2 mapping.
         */
        dsb(ish);

        /*
         * Invalidate all stage-1 TLB entries. If the CPU has a combined
         * TLB for stage-1 and stage-2, this will invalidate stage-2 as
         * well.
         */
        tlbi(vmalle1is);
    }

    /* Sync data accesses with TLB invalidation completion. */
    dsb(ish);

    /* Sync instruction fetches with TLB invalidation completion. */
    isb();
}

   *)

  Definition arch_mm_invalidate_stage2_range (va_begin va_end:var) (begin_v end_v:var) :=
    begin_v #= (Call "ipa_addr" [CBV va_begin]) #;
            end_v #= (Call "ipa_addr" [CBV va_end]).

  (*
/**
 * Returns the smallest cache line size of all the caches for this core.
 */
static uint16_t arch_mm_dcache_line_size(void)
{
    return CACHE_WORD_SIZE *
           (UINT16_C(1) << ((read_msr(CTR_EL0) >> 16) & 0xf));
}

   *)

  (*
void arch_mm_flush_dcache(void *base, size_t size)
{
    /* Clean and invalidate each data cache line in the range. */
    uint16_t line_size = arch_mm_dcache_line_size();
    uintptr_t line_begin = (uintptr_t)base & ~(line_size - 1);
    uintptr_t end = (uintptr_t)base + size;

    while (line_begin < end) {
        __asm__ volatile("dc civac, %0" : : "r"(line_begin));
        line_begin += line_size;
    }
    dsb(sy);
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

  Definition arch_mm_mode_to_stage1_attrs (mode:var) (attrs:var) :=
    attrs #= 0 #;
          attrs #= attrs #| (STAGE1_AF #| (STAGE1_SH OUTER_SHAREABLE)) #;
          (#if (#! (mode #& MM_MODE_X))
            then (attrs #= attrs #| STAGE1_XN)
            else Skip) #;
          (#if (mode #& MM_MODE_W)
            then (attrs #= attrs #| (STAGE1_AP STAGE1_READWRITE))
            else (attrs #= attrs #| (STAGE1_AP STAGE1_READONLY))) #;
          (#if (mode #& MM_MODE_D)
            then (attrs #= attrs #| (STAGE1_ATTRINDX STAGE1_DEVICEINDX))
            else (attrs #= attrs #| (STAGE1_ATTRINDX STAGE1_NORMALINDX))) #;
          (#if (#! (mode #& MM_MODE_INVALID))
            then (attrs #= attrs #| PTE_VALID)
            else Skip) #;
          Return attrs.

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

  Definition arch_mm_mode_to_stage2_attrs (mode:var) (attrs access:var) :=
    attrs #= 0 #;
          access #= 0 #;
          attrs #= attrs #| (STAGE2_AF #| (STAGE2_SH NON_SHAREABLE)) #;
          (#if (mode #& MM_MODE_R)
            then (access #= access #| STAGE2_ACCESS_READ)
            else Skip) #;
          (#if (mode #& MM_MODE_W)
            then (access #= access #| STAGE2_ACCESS_WRITE)
            else Skip) #;
          attrs #= attrs #| (STAGE2_S2AP access) #;
          (#if (mode #& MM_MODE_X)
            then (attrs #= attrs #| (STAGE2_XN STAGE2_EXECUTE_ALL))
            else (attrs #= attrs #| (STAGE2_XN STAGE2_EXECUTE_NONE))) #;
          (#if (mode #& MM_MODE_D)
            then (attrs #= attrs #| (STAGE2_MEMATTR STAGE2_DEVICE_MEMORY STAGE2_MEMATTR_DEVICE_GRE))
            else (attrs #= attrs #| (STAGE2_MEMATTR STAGE2_WRITEBACK STAGE2_WRITEBACK))) #;
          (#if (#! (mode #& MM_MODE_UNOWNED))
            then (attrs #= attrs #| STAGE2_SW_OWNED)
            else Skip) #;
          (#if (#! (mode #& MM_MODE_SHARED))
            then (attrs #= attrs #| STAGE2_SW_EXCLUSIVE)
            else Skip) #;
          (#if (#! (mode #& MM_MODE_INVALID))
            then (attrs #= attrs #| PTE_VALID)
            else Skip) #;
          Return attrs.

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

  Definition arch_mm_stage2_attrs_to_mode (attrs:var) (mode:var) :=
    mode #= 0 #;
         (#if (attrs #& (STAGE2_S2AP STAGE2_ACCESS_READ))
           then (mode #= mode #| MM_MODE_R)
           else Skip) #;
         (#if (attrs #& (STAGE2_S2AP STAGE2_ACCESS_WRITE))
           then (mode #= mode #| MM_MODE_W)
           else Skip) #;
         (#if ((attrs #& (STAGE2_XN STAGE2_EXECUTE_MASK)) == (STAGE2_XN STAGE2_EXECUTE_ALL))
           then (mode #= mode #| MM_MODE_X)
           else Skip) #;
         (#if ((attrs #& STAGE2_MEMATTR_TYPE_MASK) == STAGE2_DEVICE_MEMORY)
           then (mode #= mode #| MM_MODE_D)
           else Skip) #;
         (#if (#! (attrs #& STAGE2_SW_OWNED))
           then (mode #= mode #| MM_MODE_UNOWNED)
           else Skip) #;
         (#if (#! (attrs #& STAGE2_SW_EXCLUSIVE))
           then (mode #= mode #| MM_MODE_SHARED)
           else Skip) #;
         (#if (#! (attrs #& PTE_VALID))
           then (mode #= mode #| MM_MODE_INVALID)
           else Skip) #;
         Return mode.

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
)
   *)

  Definition arch_mm_stage2_max_level := Return mm_s2_max_level.

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

  Definition arch_mm_stage2_root_table_count := Return mm_s2_root_table_count.

  (*
/**
 * Given the attrs from a table at some level and the attrs from all the blocks
 * in that table, returns equivalent attrs to use for a block which will replace
 * the entire table.
 */
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

  Definition arch_mm_combine_table_entry_attrs (table_attrs block_attrs:var) :=
    (#if (table_attrs #& TABLE_NSTABLE)
      then (block_attrs #= block_attrs #| STAGE1_NS)
      else Skip) #;       
                 (#if (table_attrs #& TABLE_APTABLE1)
                   then (block_attrs #= block_attrs #| STAGE1_AP2)
                   else Skip) #;
                 (#if (table_attrs #& TABLE_APTABLE0)
                   then (block_attrs #= block_attrs #& (Not STAGE1_AP1))
                   else Skip) #;
                 (#if (table_attrs #& TABLE_XNTABLE)
                   then (block_attrs #= block_attrs #| STAGE1_XN)
                   else Skip) #;
                 (#if (table_attrs #& TABLE_PXNTABLE)
                   then (block_attrs #= block_attrs #| STAGE1_PXN)
                   else Skip) #;
                 Return block_attrs.

(*

/**
 * This is called early in initialization without MMU or caches enabled.
 */
bool arch_mm_init(paddr_t table)
{
    static const int pa_bits_table[16] = {32, 36, 40, 42, 44, 48};
    uint64_t features = read_msr(id_aa64mmfr0_el1);
    int pa_bits = pa_bits_table[features & 0xf];
    int extend_bits;
    int sl0;

    /* Check that 4KB granules are supported. */
    if ((features >> 28) & 0xf) {
        dlog_error("4KB granules are not supported\n");
        return false;
    }

    /* Check the physical address range. */
    if (!pa_bits) {
        dlog_error(
            "Unsupported value of id_aa64mmfr0_el1.PARange: %x\n",
            features & 0xf);
        return false;
    }

    dlog_info("Supported bits in physical address: %d\n", pa_bits);

    /*
     * Determine sl0, starting level of the page table, based on the number
     * of bits. The value is chosen to give the shallowest tree by making
     * use of concatenated translation tables.
     *
     *  - 0 => start at level 1
     *  - 1 => start at level 2
     *  - 2 => start at level 3
     */
    if (pa_bits >= 44) {
        sl0 = 2;
        mm_s2_max_level = 3;
    } else if (pa_bits >= 35) {
        sl0 = 1;
        mm_s2_max_level = 2;
    } else {
        sl0 = 0;
        mm_s2_max_level = 1;
    }

    /*
     * Since the shallowest possible tree is used, the maximum number of
     * concatenated tables must be used. This means if no more than 4 bits
     * are used from the next level, they are instead used to index into the
     * concatenated tables.
     */
    extend_bits = ((pa_bits - PAGE_BITS) % PAGE_LEVEL_BITS);
    if (extend_bits > 4) {
        extend_bits = 0;
    }
    mm_s2_root_table_count = 1 << extend_bits;

    dlog_info(
        "Stage 2 has %d page table levels with %d pages at the root.\n",
        mm_s2_max_level + 1, mm_s2_root_table_count);

    arch_mm_config = (struct arch_mm_config){
        .ttbr0_el2 = pa_addr(table),

        .vtcr_el2 =
            (1U << 31) |           /* RES1. */
            ((features & 0xf) << 16) | /* PS, matching features. */
            (0 << 14) |        /* TG0: 4 KB granule. */
            (3 << 12) |        /* SH0: inner shareable. */
            (1 << 10) |  /* ORGN0: normal, cacheable ... */
            (1 << 8) |   /* IRGN0: normal, cacheable ... */
            (sl0 << 6) | /* SL0. */
            ((64 - pa_bits) << 0) | /* T0SZ: dependent on PS. */
            0,

        /*
         * 0    -> Device-nGnRnE memory
         * 0xff -> Normal memory, Inner/Outer Write-Back Non-transient,
         *         Write-Alloc, Read-Alloc.
         */
        .mair_el2 = (0 << (8 * STAGE1_DEVICEINDX)) |
                (0xff << (8 * STAGE1_NORMALINDX)),

        /*
         * Configure tcr_el2.
         */
        .tcr_el2 =
            (1 << 20) |        /* TBI, top byte ignored. */
            ((features & 0xf) << 16) | /* PS. */
            (0 << 14) |        /* TG0, granule size, 4KB. */
            (3 << 12) |        /* SH0, inner shareable. */
            (1 << 10) | /* ORGN0, normal mem, WB RA WA Cacheable. */
            (1 << 8) |  /* IRGN0, normal mem, WB RA WA Cacheable. */
            (25 << 0) | /* T0SZ, input address is 2^39 bytes. */
            0,

        .sctlr_el2 = get_sctlr_el2_value(),
    };

    return true;
}

 *)  


  (* Test auxiliary functions in mm module *)
  Definition arch_mm_absent_pteF : function.
    mk_function_tac arch_mm_absent_pte ["level"] ([]: list var).
  Defined.

  Definition arch_mm_table_pteF : function.
    mk_function_tac arch_mm_table_pte ["level" ; "pa"] ["pa_add_res" ; "pte_table_res" ; "res"].
  Defined.

  Definition arch_mm_block_pteF : function.
    mk_function_tac arch_mm_block_pte ["level" ; "pa" ; "attrs"] ["pa_addr_res" ; "pte"].
  Defined.

  Definition arch_mm_is_block_allowedF : function.
    mk_function_tac arch_mm_is_block_allowed ["level"] ([] : list var).
  Defined.

  Definition arch_mm_pte_is_presentF : function.
    mk_function_tac arch_mm_pte_is_present ["pte"; "level"] ["pte_valid" ; "sw_owned" ; "res"].
  Defined.


  Definition arch_mm_pte_is_validF : function.
    mk_function_tac arch_mm_pte_is_valid ["pte"; "level"] ["pte_valid"].
  Defined.
  
  Definition arch_mm_pte_is_blockF : function.
    mk_function_tac arch_mm_pte_is_block ["pte"; "level"] ["blk_allowed"; "ret"; "is_blk" ; "is_present"; "is_table"].
  Defined.

  Definition arch_mm_pte_is_tableF : function.
    mk_function_tac arch_mm_pte_is_table ["pte" ; "level"] ["is_valid"].
  Defined.

  Definition pte_addrF : function.
    mk_function_tac pte_addr ["pte"] ([] : list var).
  Defined.
  
  Definition arch_mm_clear_paF : function.
    mk_function_tac arch_mm_clear_pa ["pa"] ["adddr1" ; "addr2" ; "res"].
  Defined.

  Definition arch_mm_block_from_pteF : function.
    mk_function_tac arch_mm_block_from_pte ["pte" ; "level"] ["addr" ; "res"].
  Defined.


  Definition arch_mm_table_from_pteF : function.
    mk_function_tac arch_mm_table_from_pte ["pte" ; "level"] ["addr" ; "res"].
  Defined.
  
  Definition arch_mm_pte_attrsF : function.
    mk_function_tac arch_mm_pte_attrs ["pte" ; "level"] ([] : list var).
  Defined.

  Definition arch_mm_invalidate_stage1_rangeF : function.
    mk_function_tac arch_mm_invalidate_stage1_range ["va_begin" ; "va_end"] ["begin_v" ; "end_v"].
  Defined.

  Definition arch_mm_invalidate_stage2_rangeF : function.
    mk_function_tac arch_mm_invalidate_stage2_range ["va_begin" ; "va_end"] ["begin_v" ; "end_v"].
  Defined.

  Definition arch_mm_mode_to_stage1_attrsF : function.
    mk_function_tac arch_mm_mode_to_stage1_attrs ["mode"] ["attrs"].
  Defined.

  Definition arch_mm_mode_to_stage2_attrsF : function.
    mk_function_tac arch_mm_mode_to_stage2_attrs ["mode"] ["attrs" ; "access"].
  Defined.
  
  Definition arch_mm_stage2_attrs_to_modeF : function.
    mk_function_tac arch_mm_stage2_attrs_to_mode ["attrs"] ["mode"].
  Defined.

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

  Definition arch_mm_combine_table_entry_attrsF : function.
    mk_function_tac arch_mm_combine_table_entry_attrs ["table_attrs" ; "block_attrs"] ([]: list var).
  Defined.

  
  Definition arch_mm_program: program :=
    [
      ("arch_mm_absent_pte", arch_mm_absent_pteF) ;
    ("arch_mm_table_pte", arch_mm_table_pteF) ;
    ("arch_mm_block_pte", arch_mm_block_pteF) ;
    ("arch_mm_is_block_allowed", arch_mm_is_block_allowedF) ;
    ("arch_mm_pte_is_present", arch_mm_pte_is_presentF) ;
    ("arch_mm_pte_is_valid", arch_mm_pte_is_validF) ;
    ("arch_mm_pte_is_block", arch_mm_pte_is_blockF) ;
    ("arch_mm_pte_is_table", arch_mm_pte_is_tableF) ;
    ("pte_addr", pte_addrF) ;
    ("arch_mm_clear_pa", arch_mm_clear_paF) ;
    ("arch_mm_block_from_pte", arch_mm_block_from_pteF) ;
    ("arch_mm_table_from_pte", arch_mm_table_from_pteF) ;
    ("arch_mm_pte_attrs", arch_mm_pte_attrsF) ;
    ("arch_mm_invalidate_stage1_range", arch_mm_invalidate_stage1_rangeF) ;
    ("arch_mm_invalidate_stage2_range", arch_mm_invalidate_stage2_rangeF) ;
    ("arch_mm_mode_to_stage1_attrs", arch_mm_mode_to_stage1_attrsF) ;
    ("arch_mm_mode_to_stage2_attrs", arch_mm_mode_to_stage2_attrsF) ;
    ("arch_mm_stage2_attrs_to_mode", arch_mm_stage2_attrs_to_modeF) ;
    ("arch_mm_stage1_max_level", arch_mm_stage1_max_levelF) ;
    ("arch_mm_stage2_max_level", arch_mm_stage2_max_levelF) ;
    ("arch_mm_stage1_root_table_count", arch_mm_stage1_root_table_countF) ;
    ("arch_mm_stage2_root_table_count", arch_mm_stage2_root_table_countF) ;
    ("arch_mm_combine_table_entry_attrs", arch_mm_combine_table_entry_attrsF)
    ].

  Definition arch_mm_modsem :=  program_to_ModSem arch_mm_program.

End ArchMM.



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

Require Import Coq.NArith.BinNat.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Constants.
Require Import Hafnium.Concrete.Assumptions.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Addr.

(*** This file defines (the necessary parts of) the API provided by arch/mm.h,
     which is assumed correct for now. In order to replace this assumption with
     a proof of correctness, replace the [Axiom]s with definitions and proofs,
     leaving their types the same. ***)

(* levels are represented by natural numbers, but just to make it
   extra clear we give them an alias to differentiate them from
   other [nat]s *)
Local Notation level := nat.

Axiom arch_mm_absent_pte : level -> pte_t.

Axiom arch_mm_block_pte : level -> paddr_t -> attributes -> pte_t.

(* N.B. we take in a ptable_pointer instead of a paddr_t here *)
Axiom arch_mm_table_pte : level -> ptable_pointer -> pte_t.

Axiom arch_mm_pte_is_present : pte_t -> level -> bool.

Axiom arch_mm_pte_is_valid : pte_t -> level -> bool.

Axiom arch_mm_pte_is_block : pte_t -> level -> bool.

Axiom arch_mm_pte_is_table : pte_t -> level -> bool.

Axiom arch_mm_table_from_pte : pte_t -> level -> paddr_t.

Axiom arch_mm_pte_attrs : pte_t -> level -> attributes.

Axiom arch_mm_stage2_attrs_to_mode : attributes -> mode_t.

Axiom arch_mm_stage2_max_level : level.

Axiom arch_mm_stage1_max_level : level.

Axiom arch_mm_stage2_root_table_count : nat.

Axiom arch_mm_stage1_root_table_count : nat.

Axiom arch_mm_mode_to_stage1_attrs : mode_t -> attributes.

Axiom arch_mm_mode_to_stage2_attrs : mode_t -> attributes.

Axiom arch_mm_clear_pa : paddr_t -> paddr_t.

Axiom arch_mm_is_block_allowed : level -> bool.

Axiom arch_mm_block_from_pte : pte_t -> level -> paddr_t.

Axiom arch_mm_combine_table_entry_attrs : attributes -> attributes -> attributes.


(* Assumptions about the properties of arch/mm.c *)
Axiom stage1_root_table_count_ok : arch_mm_stage1_root_table_count < Nat.pow 2 PAGE_LEVEL_BITS.
Axiom stage2_root_table_count_ok : arch_mm_stage2_root_table_count < Nat.pow 2 PAGE_LEVEL_BITS.
Axiom stage1_max_level_pos : 0 < arch_mm_stage1_max_level.
Axiom stage2_max_level_pos : 0 < arch_mm_stage2_max_level.

(* absent and block PTEs are not tables *)
Axiom absent_not_table :
  forall level,
    arch_mm_pte_is_table (arch_mm_absent_pte level) level = false.
Axiom block_not_table :
  forall level pa attrs,
    arch_mm_pte_is_table (arch_mm_block_pte level pa attrs) level = false.

(* shorthand definitions just for this file to make axiom statements neater *)
Local Notation get_bit n bit := (negb (N.eqb (N.land n bit) 0)). (* (n & bit) != 0 *)

(* arch_mm_pte_is_valid is true iff [ attrs & PTE_VALID != 0 ] *)
Axiom is_valid_matches_flag :
  forall pte level,
    let attrs := arch_mm_pte_attrs pte level in
    arch_mm_pte_is_valid pte level = get_bit attrs PTE_VALID.

(* arch_mm_pte_is_present returns true iff the valid bit is 0 or the stage-2
   owned bit is true *)
Axiom is_present_iff :
  forall pte level,
    let attrs := arch_mm_pte_attrs pte level in
    let mode := arch_mm_stage2_attrs_to_mode attrs in
    arch_mm_pte_is_present pte level =
    (get_bit attrs PTE_VALID || get_bit mode MM_MODE_UNOWNED)%bool.

(* when attributes are converted to a stage-2 mode, the valid bit matches *)
Axiom stage2_attrs_to_mode_valid :
  forall attrs,
    ((N.land attrs PTE_VALID) =? 0)%N =
    get_bit (arch_mm_stage2_attrs_to_mode attrs) MM_MODE_INVALID.

(* absent PTEs don't have the valid bit set *)
Axiom absent_invalid :
  forall level, arch_mm_pte_is_valid (arch_mm_absent_pte level) level = false.

(* we assume there exists some set of attributes that we can use which is neither
   valid nor stage-2 owned *)
Axiom absent_attrs : attributes.
Axiom absent_attrs_invalid : get_bit absent_attrs PTE_VALID = false.
Axiom absent_attrs_unowned :
  get_bit (arch_mm_stage2_attrs_to_mode absent_attrs) MM_MODE_UNOWNED = true.
 *)

