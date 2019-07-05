Require Import Coq.NArith.BinNat.
Require Import Coq.Lists.List.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Notations.
Require Import Hafnium.Concrete.State.
Require Import Hafnium.Util.Loops.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.ArchMM.
Require Import Hafnium.Concrete.Assumptions.Constants.
Require Import Hafnium.Concrete.Assumptions.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Mpool.
Require Import Hafnium.Concrete.MM.Datatypes.

(*** This file transcribes necessary functions from mm.c, with the original C in
     comments alongside. ***)

(* typedef uintvaddr_t ptable_addr_t; *)
Definition ptable_addr_t : Type := uintvaddr_t.
Bind Scope N_scope with ptable_addr_t.

(*
/**
 * Get the page table from the physical address.
 */
static struct mm_page_table *mm_page_table_from_pa(paddr_t pa) *)
Definition mm_page_table_from_pa (pa : paddr_t) : ptable_pointer :=
  (* return ptr_from_va(va_from_pa(pa)); *)
  ptr_from_va (va_from_pa pa).

(* static ptable_addr_t mm_round_down_to_page(ptable_addr_t addr) *)
Definition mm_round_down_to_page (addr : ptable_addr_t) : ptable_addr_t :=
  (* return addr & ~((ptable_addr_t)(PAGE_SIZE - 1)); *)
  addr &~ (PAGE_SIZE - 1).

(* static ptable_addr_t mm_round_up_to_page(ptable_addr_t addr) *)
Definition mm_round_up_to_page (addr : ptable_addr_t) : ptable_addr_t :=
  (* return mm_round_down_to_page(addr + PAGE_SIZE - 1); *)
  mm_round_down_to_page (addr + PAGE_SIZE - 1).

(*
/**
 * Calculates the size of the address space represented by a page table entry at
 * the given level.
 */
static size_t mm_entry_size(uint8_t level)  *)
Definition mm_entry_size (level : nat) : size_t :=
  (* return UINT64_C(1) << (PAGE_BITS + level * PAGE_LEVEL_BITS); *)
  N.to_nat (1 << (PAGE_BITS + level * PAGE_LEVEL_BITS)).

(*
/**
 * Gets the address of the start of the next block of the given size. The size
 * must be a power of two.
 */
static ptable_addr_t mm_start_of_next_block(ptable_addr_t addr,
                                            size_t block_size) *)
Definition mm_start_of_next_block (addr : ptable_addr_t) (block_size : size_t)
  : ptable_addr_t :=
  (* return (addr + block_size) & ~(block_size - 1); *)
  (addr + block_size) &~ (block_size - 1).

(*
/**
 * Gets the physical address of the start of the next block of the given size.
 * The size must be a power of two.
 */
static paddr_t mm_pa_start_of_next_block(paddr_t pa, size_t block_size) *)
Definition mm_pa_start_of_next_block (pa : paddr_t) (block_size : size_t)
  : paddr_t :=
  (* return pa_init((pa_addr(pa) + block_size) & ~(block_size - 1)); *)
  pa_init (pa_addr pa + block_size &~ (block_size - 1)).

(*
/**
 * For a given address, calculates the maximum (plus one) address that can be
 * represented by the same table at the given level.
 */
static ptable_addr_t mm_level_end(ptable_addr_t addr, uint8_t level) *)
Definition mm_level_end (addr : ptable_addr_t) (level : nat) : ptable_addr_t :=
  (* size_t offset = PAGE_BITS + (level + 1) * PAGE_LEVEL_BITS; *)
  let offset : size_t := PAGE_BITS + (level + 1) * PAGE_LEVEL_BITS in

  (* return ((addr >> offset) + 1) << offset; *)
  ((addr >> offset) + 1) << offset.

(*
/**
 * For a given address, calculates the index at which its entry is stored in a
 * table at the given level.
 */
static size_t mm_index(ptable_addr_t addr, uint8_t level)
 *)
Definition mm_index (addr : ptable_addr_t) (level : nat) : size_t :=
  (* ptable_addr_t v = addr >> (PAGE_BITS + level * PAGE_LEVEL_BITS); *)
  let v : ptable_addr_t := (addr >> (PAGE_BITS + level * PAGE_LEVEL_BITS))%N in

  (* return v & ((UINT64_C(1) << PAGE_LEVEL_BITS) - 1); *)
  N.to_nat (v & ((1 << PAGE_LEVEL_BITS) - 1)).

(*
/**
 * Returns the maximum level in the page table given the flags.
 */
static uint8_t mm_max_level(int flags) *)
Definition mm_max_level (flags : int) : nat :=
  (* return (flags & MM_FLAG_STAGE1) ? arch_mm_stage1_max_level()
                                     : arch_mm_stage2_max_level(); *)
  if ((flags & MM_FLAG_STAGE1) =? 0)%N
  then arch_mm_stage2_max_level
  else arch_mm_stage1_max_level.

(*
/**
 * Returns the number of root-level tables given the flags.
 */
static uint8_t mm_root_table_count(int flags) *)
Definition mm_root_table_count (flags : int) : nat :=
  (* return (flags & MM_FLAG_STAGE1) ? arch_mm_stage1_root_table_count()
                                     : arch_mm_stage2_root_table_count(); *)
  if ((flags & MM_FLAG_STAGE1) =? 0)%N
  then arch_mm_stage2_root_table_count
  else arch_mm_stage1_root_table_count.

(*
/**
 * Frees all page-table-related memory associated with the given pte at the
 * given level, including any subtables recursively.
 */
static void mm_free_page_pte(pte_t pte, uint8_t level, struct mpool *ppool) *)
Fixpoint mm_free_page_pte
           (s : concrete_state) (pte : pte_t) (level : nat) (ppool : mpool)
  : concrete_state * mpool :=

  (* if (!arch_mm_pte_is_table(pte, level)) {
             return;
     } *)
  if (!(arch_mm_pte_is_table pte level))%bool
  then (s, ppool)
  else
    match level with
    | 0 =>
      (* shouldn't get here. since the entry is a table *)
      (s, ppool)
    | S level_minus1 =>

      (* /* Recursively free any subtables. */
         table = mm_page_table_from_pa(arch_mm_table_from_pte(pte, level)); *)
      let table :=
          (mm_page_table_from_pa (arch_mm_table_from_pte pte level)) in

      (* for (i = 0; i < MM_PTE_PER_PAGE; ++i) {
                  mm_free_page_pte(table->entries[i], level - 1, ppool);
         } *)
      let '(s, ppool) :=
          fold_right
            (fun i '(s, ppool) =>
               mm_free_page_pte
                 s ((s.(ptable_deref) table)[[i]]) level_minus1 ppool)
            (s, ppool)
            (seq 0 MM_PTE_PER_PAGE) in

    (* /* Free the table itself. */
       mpool_free(ppool, table); *)
    let ppool := mpool_free ppool table in
    (s, ppool)
    end.


(*
/**
 * Replaces a page table entry with the given value. If both old and new values
 * are valid, it performs a break-before-make sequence where it first writes an
 * invalid value to the PTE, flushes the TLB, then writes the actual new value.
 * This is to prevent cases where CPUs have different 'valid' values in their
 * TLBs, which may result in issues for example in cache coherency.
 */
static void mm_replace_entry(ptable_addr_t begin, pte_t *pte, pte_t new_pte,
			     uint8_t level, int flags, struct mpool *ppool) *)
Definition mm_replace_entry
           (s : concrete_state)
           (begin : ptable_addr_t)
           (pte new_pte : pte_t)
           (level : nat)
           (flags : int)
           (ppool : mpool) : concrete_state * mpool :=
  (s, ppool). (* TODO *)

(*
/**
 * Populates the provided page table entry with a reference to another table if
 * needed, that is, if it does not yet point to another table.
 *
 * Returns a pointer to the table the entry now points to.
 */
static struct mm_page_table *mm_populate_table_pte(ptable_addr_t begin,
						   pte_t *pte, uint8_t level,
						   int flags,
						   struct mpool *ppool) *)
Definition mm_populate_table_pte
           (s : concrete_state)
           (begin : ptable_addr_t)
           (pte : pte_t)
           (level : nat)
           (flags : int)
           (ppool : mpool) : option mm_page_table * concrete_state * mpool :=
  (None, s, ppool). (* TODO *)

(*
/**
 * Returns whether all entries in this table are absent.
 */
static bool mm_page_table_is_empty(struct mm_page_table *table, uint8_t level) *)
Definition mm_page_table_is_empty(table : mm_page_table) (level : nat) : bool :=
  false. (* TODO *)

(*
/**
 * Updates the page table at the given level to map the given address range to a
 * physical range using the provided (architecture-specific) attributes. Or if
 * MM_FLAG_UNMAP is set, unmap the given range instead.
 *
 * This function calls itself recursively if it needs to update additional
 * levels, but the recursion is bound by the maximum number of levels in a page
 * table.
 */
static bool mm_map_level(ptable_addr_t begin, ptable_addr_t end, paddr_t pa,
                         uint64_t attrs, struct mm_page_table *table,
                         uint8_t level, int flags, struct mpool *ppool) *)
Definition mm_map_level
           (s : concrete_state)
           (begin end_ : ptable_addr_t)
           (pa : paddr_t)
           (attrs : attributes)
           (table : mm_page_table)
           (level : nat)
           (flags : int)
           (ppool : mpool) : bool * concrete_state * mpool :=

  (* pte_t *pte = &table->entries[mm_index(begin, level)]; *)
  (* N.B. storing the index instead of a pointer *)
  let pte_index := mm_index begin level in

  (* ptable_addr_t level_end = mm_level_end(begin, level); *)
  let level_end := mm_level_end begin level in

  (* size_t entry_size = mm_entry_size(level); *)
  let entry_size := mm_entry_size level in

  (* bool commit = flags & MM_FLAG_COMMIT; *)
  let commit : bool := (!((flags & MM_FLAG_COMMIT) =? 0)%N)%bool in

  (* bool unmap = flags & MM_FLAG_UNMAP; *)
  let unmap : bool := (!((flags & MM_FLAG_UNMAP) =? 0)%N)%bool in

  (* /* Cap end so that we don't go over the current level max. */
        if (end > level_end) {
                end = level_end;
        } *)
  let end_ := N.min level_end end_ in

  (* /* Fill each entry in the table. */
     while (begin < end) { *)
  let '(s, begin, pa, pte_index, failed, ppool) :=
      while_loop
        (max_iterations := N.to_nat (end_ - begin))
        (fun _ => (begin <? end_)%N)
        (s, begin, pa, pte_index, false, ppool)
        (fun '(s, begin, pa, pte_index, failed, ppool) =>
           let pte := table[[ pte_index ]] in

           (* if (unmap ? !arch_mm_pte_is_present( *pte, level)
                        : arch_mm_pte_is_block( *pte, level) &&
                                  arch_mm_pte_attrs( *pte, level) == attrs) {
                      /*
                       * If the entry is already mapped with the right
                       * attributes, or already absent in the case of
                       * unmapping, no need to do anything; carry on to the
                       * next entry.
                       */ *)
           if ((if unmap
                then !arch_mm_pte_is_present pte level
                else arch_mm_pte_is_block pte level)
                 && (arch_mm_pte_attrs pte level =? attrs)%N)%bool
           then
             (* done; continue to the next entry *)
             (* begin = mm_start_of_next_block(begin, entry_size);
                pa = mm_pa_start_of_next_block(pa, entry_size);
                pte++; *)
             let begin := mm_start_of_next_block begin entry_size in
             let pa := mm_pa_start_of_next_block pa entry_size in
             let pte_index := S pte_index in
             (s, begin, pa, pte_index, failed, ppool, continue)
           else
             (* } else if ((end - begin) >= entry_size &&
                  (unmap || arch_mm_is_block_allowed(level)) &&
                  (begin & (entry_size - 1)) == 0) { *)
             if ((entry_size <=? (end_ - begin))%N
                   && (unmap || arch_mm_is_block_allowed level)
                   && ((begin & (entry_size - 1)) =? 0)%N)%bool
             then
               (* /*
                   * If the entire entry is within the region we want to
                   * map, map/unmap the whole entry.
                   */
                  if (commit) {
                          pte_t new_pte =
                                  unmap ? arch_mm_absent_pte(level)
                                        : arch_mm_block_pte(level, pa,
                                                            attrs);
                          mm_replace_entry(begin, pte, new_pte, level,
                                           flags, ppool);
                  } *)
               let '(s, ppool) :=
                   if commit
                   then let new_pte := if unmap
                                       then arch_mm_absent_pte level
                                       else arch_mm_block_pte level pa attrs in
                        mm_replace_entry s begin pte new_pte level flags ppool
                   else (s, ppool) in

               (* done; continue to the next entry *)
               (* begin = mm_start_of_next_block(begin, entry_size);
                  pa = mm_pa_start_of_next_block(pa, entry_size);
                  pte++; *)
               let begin := mm_start_of_next_block begin entry_size in
               let pa := mm_pa_start_of_next_block pa entry_size in
               let pte_index := S pte_index in
               (s, begin, pa, pte_index, failed, ppool, continue)
             else
               (* /*
                   * If the entry is already a subtable get it; otherwise
                   * replace it with an equivalent subtable and get that.
                   */
                  struct mm_page_table *nt = mm_populate_table_pte(
                          begin, pte, level, flags, ppool); *)
               let '(nt, s, ppool) :=
                   mm_populate_table_pte s begin pte level flags ppool in

               (* if (nt == NULL) {
                          return false;
                  } *)
               match nt with
               | None =>
                 let failed := true in
                 (s, begin, pa, pte_index, failed, ppool, break)
               | Some nt =>
                 (* /*
                  * If the subtable is now empty, replace it with an
                  * absent entry at this level. We never need to do
                  * break-before-makes here because we are assigning
                  * an absent value.
                  */
                     if (commit && unmap &&
                         mm_page_table_is_empty(nt, level - 1)) {
                             pte_t v = *pte;
                             *pte = arch_mm_absent_pte(level);
                             mm_free_page_pte(v, level, ppool);
                     } *)
                 let '(pte, s, ppool) :=
                     if (commit && unmap &&
                                mm_page_table_is_empty nt (level - 1))%bool
                     then
                       let v := pte in
                       let pte := arch_mm_absent_pte level in
                       let '(s, ppool) := mm_free_page_pte s v level ppool in
                       (pte, s, ppool)
                     else (pte, s, ppool) in
                 (* done; continue to the next entry *)
                 (* begin = mm_start_of_next_block(begin, entry_size);
                    pa = mm_pa_start_of_next_block(pa, entry_size);
                    pte++; *)
                 let begin := mm_start_of_next_block begin entry_size in
                 let pa := mm_pa_start_of_next_block pa entry_size in
                 let pte_index := S pte_index in
                 (s, begin, pa, pte_index, failed, ppool, continue)
               end) in

  (* return true; *)
  (* N.B. have to check here if the loop returned false partway through *)
  let success := (!failed)%bool in
  (success, s, ppool).

(*
/**
 * Updates the page table from the root to map the given address range to a
 * physical range using the provided (architecture-specific) attributes. Or if
 * MM_FLAG_UNMAP is set, unmap the given range instead.
 */
static bool mm_map_root(struct mm_ptable *t, ptable_addr_t begin,
                        ptable_addr_t end, uint64_t attrs, uint8_t root_level,
                        int flags, struct mpool *ppool) *)
Definition mm_map_root
           (s : concrete_state)
           (t : mm_ptable)
           (begin end_ : ptable_addr_t)
           (attrs : attributes)
           (root_level : nat)
           (flags : int)
           (ppool : mpool) : bool * concrete_state * mpool :=
  (* size_t root_table_size = mm_entry_size(root_level); *)
  let root_table_size := mm_entry_size root_level in

  (* struct mm_page_table *table =
             &mm_page_table_from_pa(t->root)[mm_index(begin, root_level)]; *)
  let table :=
      (s.(ptable_deref)
           (mm_page_table_from_pa
              t.(root))) {{ (mm_index begin root_level) }} in

  (* while (begin < end) { *)
  let '(s, begin, table, failed, ppool) :=
      while_loop
        (max_iterations := N.to_nat (end_ - begin))
        (fun _ => (begin <? end_)%N)
        (s, begin, table, false, ppool)
        (fun '(s, begin, table, failed, ppool) =>

           (* if (!mm_map_level(begin, end, pa_init(begin), attrs, table,
                                  root_level - 1, flags, ppool)) {
                      return false;
              } *)
           match mm_map_level s begin end_ (pa_init begin) attrs table
                              (root_level - 1) flags ppool with
           | (false, s, ppool) =>
             let failed := true in
             (s, begin, table, failed, ppool, break)
           | (true, s, ppool) =>

             (* begin = mm_start_of_next_block(begin, root_table_size); *)
             let begin := mm_start_of_next_block begin root_table_size in

             (* table++; *)
             let table := table {{ 1 }} in

             (s, begin, table, failed, ppool, continue)
           end) in

  (* return true; *)
  (* N.B. we have to check here if the while loop failed partway through *)
  let success := (!failed)%bool in
  (success, s, ppool).

(*
/**
 * Updates the given table such that the given physical address range is mapped
 * or not mapped into the address space with the architecture-agnostic mode
 * provided.
 */
static bool mm_ptable_identity_update(struct mm_ptable *t, paddr_t pa_begin,
                                      paddr_t pa_end, uint64_t attrs, int flags,
                                      struct mpool *ppool) *)
Definition mm_ptable_identity_update
           (s : concrete_state)
           (t : mm_ptable)
           (pa_begin pa_end : paddr_t)
           (attrs : attributes)
           (flags : int)
           (ppool : mpool) : bool * concrete_state * mpool :=
  (* uint8_t root_level = mm_max_level(flags) + 1; *)
  let root_level := mm_max_level flags + 1 in

  (* ptable_addr_t ptable_end =
             mm_root_table_count(flags) * mm_entry_size(root_level); *)
  let ptable_end := mm_root_table_count flags * mm_entry_size root_level in

  (* ptable_addr_t end = mm_round_up_to_page(pa_addr(pa_end)); *)
  let end_ := mm_round_up_to_page (pa_addr pa_end) in

  (* ptable_addr_t begin = pa_addr(arch_mm_clear_pa(pa_begin)); *)
  let begin := pa_addr (arch_mm_clear_pa pa_begin) in

  (* assert(root_level >= 2); *)
  (* SKIPPED *)

  (* /* Cap end to stay within the bounds of the page table. */
     if (end > ptable_end) {
             end = ptable_end;
     } *)
  let end_ := N.min ptable_end end_ in

  (* /*
      * Do it in two steps to prevent leaving the table in a halfway updated
      * state. In such a two-step implementation, the table may be left with
      * extra internal tables, but no different mapping on failure.
      */
     if (!mm_map_root(t, begin, end, attrs, root_level, flags, ppool) ||
         !mm_map_root(t, begin, end, attrs, root_level,
                      flags | MM_FLAG_COMMIT, ppool)) {
             return false;
     } *)
  match mm_map_root s t begin end_ attrs root_level flags ppool with
  | (false, s, ppool) => (false, s, ppool)
  | (true, s, ppool) =>
    let flags := (flags ||| MM_FLAG_COMMIT)%N in
    match mm_map_root s t begin end_ attrs root_level flags ppool with
    | (false, s, ppool) => (false, s, ppool)
    | (true, s, ppool) =>
      (* /* Invalidate the tlb. */
         if ((flags & MM_FLAG_STAGE1) || mm_stage2_invalidate) {
                 mm_invalidate_tlb(begin, end, flags);
         } *)
      (* N.B. we're not yet modelling the TLB or cache, but should probably do so
         in the future. *)
      (* SKIPPED *)

      (* return true; *)
      (true, s, ppool)
    end
  end.

(*
/**
 * Gets the attributes applied to the given range of stage-2 addresses at the
 * given level.
 *
 * The `got_attrs` argument is initially passed as false until `attrs` contains
 * attributes of the memory region at which point it is passed as true.
 *
 * The value returned in `attrs` is only valid if the function returns true.
 *
 * Returns true if the whole range has the same attributes and false otherwise.
 */
static bool mm_ptable_get_attrs_level(struct mm_page_table *table,
                                      ptable_addr_t begin, ptable_addr_t end,
                                      uint8_t level, bool got_attrs,
                                      uint64_t *attrs) *)
Fixpoint mm_ptable_get_attrs_level
           (ptable_deref : ptable_pointer -> mm_page_table)
           (table : mm_page_table)
           (begin end_ : ptable_addr_t)
           (level : nat)
           (got_attrs : bool)
           (attrs : attributes)
  : bool * attributes :=
  (* pte_t *pte = &table->entries[mm_index(begin, level)]; *)
  (* N.B. I'm storing the index instead of a pointer *)
  let pte_index := mm_index begin level in

  (* ptable_addr_t level_end = mm_level_end(begin, level); *)
  let level_end := mm_level_end begin level in

  (* size_t entry_size = mm_entry_size(level); *)
  let entry_size := mm_entry_size level in

  (* /* Cap end so that we don't go over the current level max. */
     if (end > level_end) {
             end = level_end;
     } *)
  let end_ := if (level_end <? end_)%N then level_end else end_ in

  (* /* Check that each entry is owned. */
     while (begin < end) { *)
  let '(begin, pte_index, got_attrs, attrs) :=
      while_loop
        (max_iterations := N.to_nat (end_ - begin))
        (fun _ => (begin <? end_)%N)
        (begin, pte_index, got_attrs, attrs)
        (fun '(begin, pte_index, got_attrs, attrs) =>
           let pte := table[[ pte_index ]] in
           if arch_mm_pte_is_table pte level
           then
             match level with
             | 0 =>
               (* shouldn't get here -- no tables at level 0 *)
               (begin, pte_index, got_attrs, attrs, break)
             | S (level_minus1) =>
               (* if (!mm_ptable_get_attrs_level(
                           mm_page_table_from_pa(
                                   arch_mm_table_from_pte( *pte,
                                                          level)),
                           begin, end, level - 1, got_attrs, attrs)) {
                         return false;
                     } *)
               match (mm_ptable_get_attrs_level
                        ptable_deref
                        (ptable_deref
                           (mm_page_table_from_pa
                              (arch_mm_table_from_pte pte level)))
                        begin end_ level_minus1 got_attrs attrs) with
               | (false, attrs) =>
                 let got_attrs := false in
                 (begin, pte_index, got_attrs, attrs, break)
               | (true, attrs) =>
                 (* end of case, go to end of function:

                    begin = mm_start_of_next_block(begin, entry_size);
                    pte++; *)
                 let begin := mm_start_of_next_block begin entry_size in
                 let pte_index := S pte_index in
                 (begin, pte_index, got_attrs, attrs, continue)
               end
             end
           else
             (* if (!got_attrs) {
                        *attrs = arch_mm_pte_attrs( *pte, level);
                        got_attrs = true;
                } else if (arch_mm_pte_attrs( *pte, level) != *attrs) {
                        return false;
                } *)
             if (!got_attrs)%bool
             then
               let attrs := arch_mm_pte_attrs pte level in
               let got_attrs := true in
               (* end of case, go to end of function:

                  begin = mm_start_of_next_block(begin, entry_size);
                  pte++; *)
               let begin := mm_start_of_next_block begin entry_size in
               let pte_index := S pte_index in
               (begin, pte_index, got_attrs, attrs, continue)
             else if (!(arch_mm_pte_attrs pte level =? attrs)%N)%bool
                  then
                    let got_attrs := false in
                    (begin, pte_index, got_attrs, attrs, break)
                  else
                    (* end of case, go to end of function:

                       begin = mm_start_of_next_block(begin, entry_size);
                       pte++; *)
                    let begin := mm_start_of_next_block begin entry_size in
                    let pte_index := S pte_index in
                    (begin, pte_index, got_attrs, attrs, continue)) in
  (* return got_attrs *)
  (got_attrs, attrs).

(*
/**
* Gets the attributes applies to the given range of addresses in the stage-2
* table.
*
* The value returned in `attrs` is only valid if the function returns true.
*
* Returns true if the whole range has the same attributes and false otherwise.
*/
static bool mm_vm_get_attrs(struct mm_ptable *t, ptable_addr_t begin,
                            ptable_addr_t end, uint64_t *attrs) *)
Definition mm_vm_get_attrs
           (s : concrete_state)
           (t : mm_ptable)
           (begin end_ : ptable_addr_t) : bool * attributes :=

  (* int flags = 0; *)
  let flags : int := 0 in

  (* uint8_t max_level = mm_max_level(flags); *)
  let max_level := mm_max_level flags in

  (* uint8_t root_level = max_level + 1; *)
  let root_level := max_level + 1 in

  (* size_t root_table_size = mm_entry_size(root_level); *)
  let root_table_size : size_t := mm_entry_size root_level in

  (* ptable_addr_t ptable_end =
          mm_root_table_count(flags) * mm_entry_size(root_level); *)
  let ptable_end := mm_root_table_count flags * mm_entry_size root_level in

  (* bool got_attrs = false; *)
  let got_attrs := false in

  (* begin = mm_round_down_to_page(begin); *)
  let begin := mm_round_down_to_page begin in

  (* end = mm_round_up_to_page(end); *)
  let end_ := mm_round_up_to_page(end_) in

  (* /* Fail if the addresses are out of range. */
     if (end > ptable_end) {
             return false;
     } *)
  if (ptable_end <? end_)%N
  then (false, 0%N)
  else

    (* N.B. see note in MM/Datatypes.v about index into mm_page_table struct *)
    (* table = &mm_page_table_from_pa(t->root)[mm_index(begin, root_level)]; *)
    let table :=
        (s.(ptable_deref)
             (mm_page_table_from_pa
                t.(root))) {{ (mm_index begin root_level) }} in
    (* while (begin < end) {
               if (!mm_ptable_get_attrs_level(table, begin, end, max_level,
                                              got_attrs, attrs)) {
                       return false;
               }
               got_attrs = true;
               begin = mm_start_of_next_block(begin, root_table_size);
               table++;
      } *)
    let '(_, _, got_attrs, attrs, _) :=
        fold_right
          (fun _ (state : (ptable_addr_t * mm_page_table * bool * attributes * bool)) =>
             let '(begin, table, got_attrs, attrs, loop_done) := state in
             if loop_done
             then state (* no-op *)
             else
               match mm_ptable_get_attrs_level
                       s.(ptable_deref) table begin end_ max_level got_attrs attrs with
               | (false, attrs) =>
                 (* set get_attrs to false and loop_done to true to exit and
                    return false *)
                 (begin, table, false, attrs, true)
               | (true, attrs) =>
                 let got_attrs := true in
                 let table := table{{ 1 }} in
                 let begin := mm_start_of_next_block begin root_table_size in
                 let loop_done := false in
                 (begin, table, got_attrs, attrs, loop_done)
               end)
          (begin, table, got_attrs, 0%N, false)
          (* continue running the loop a maximum of (end_ - begin) times. Since
             mm_start_of_next block increases [begin] by at least one, the loop
             will reach its exit condition before running out of fuel. *)
          (seq (N.to_nat begin) (N.to_nat end_)) in
    (got_attrs, attrs).

(*
/**
* Updates a VM's page table such that the given physical address range is
* mapped in the address space at the corresponding address range in the
* architecture-agnostic mode provided.
*/
bool mm_vm_identity_map(struct mm_ptable *t, paddr_t begin, paddr_t end,
                        int mode, ipaddr_t *ipa, struct mpool *ppool) *)
(* N.B. for now, ignoring the ipa argument, which is set to NULL in all calls
   I've found so far. *)
Definition mm_vm_identity_map
           (s : concrete_state)
           (t : mm_ptable)
           (begin : paddr_t)
           (end_ : paddr_t)
           (mode : mode_t)
           (ppool : mpool) : (bool * concrete_state * mpool) :=
  (* int flags = 0; *)
  let flags : int := 0 in

  (* bool success = mm_ptable_identity_update(
              t, begin, end, arch_mm_mode_to_stage2_attrs(mode), flags,
              ppool); *)
  let '(success, state, ppool) :=
      mm_ptable_identity_update
        s t begin end_ (arch_mm_mode_to_stage2_attrs mode) flags ppool in

  (* if (success && ipa != NULL) {
             *ipa = ipa_from_pa(begin);
     } *)
  (* Since we assume ipa = NULL, we can skip the if clause *)
  (* SKIPPED *)

  (* return success *)
  (success, state, ppool).

(*
/**
 * Defragments the VM page table.
 */
void mm_vm_defrag(struct mm_ptable *t, struct mpool *ppool) *)
Definition mm_vm_defrag
           (s : concrete_state) (t : mm_ptable) (ppool : mpool)
  : (bool * concrete_state * mpool) :=
  (false, s, ppool). (* TODO *)

(*
/**
* Gets the mode of the give range of intermediate physical addresses if they
* are mapped with the same mode.
*
* Returns true if the range is mapped with the same mode and false otherwise.
*/
bool mm_vm_get_mode(struct mm_ptable *t, ipaddr_t begin, ipaddr_t end,
     int *mode) *)
(* N.B. the comment above the function means "the entire range of addresses
   has one consistent mode" and not "the range of addresses has the same
   mode as is indicated by the pointer passed in". *)
Definition mm_vm_get_mode
           (s : concrete_state)
           (t : mm_ptable)
           (begin end_ : ipaddr_t) : bool * mode_t :=
  (false, 0%N). (* TODO *)

(*
/**
* Updates the hypervisor page table such that the given physical address range
* is mapped into the address space at the corresponding address range in the
* architecture-agnostic mode provided.
*/
void *mm_identity_map(paddr_t begin, paddr_t end, int mode, struct mpool *ppool) *)
(* N.B. the original code returns a [void *] that is NULL if the operation
   failed; we will return a boolean instead, since we don't currently ever do
   anything with the pointer except check if it's NULL. *)
Definition mm_identity_map
           (s : concrete_state)
           (begin end_ : paddr_t)
           (mode : mode_t)
           (ppool : mpool) : (bool * concrete_state * mpool) :=
  (false, s, ppool). (* TODO *)

(*
/**
 * Updates the hypervisor table such that the given physical address range is
 * not mapped in the address space.
 */
bool mm_unmap(paddr_t begin, paddr_t end, struct mpool *ppool) *)
Definition mm_unmap (s : concrete_state) (begin end_ : paddr_t) (ppool : mpool)
  : (bool * concrete_state * mpool) :=
  (false, s, ppool). (* TODO *)

(*
/**
 * Defragments the hypervisor page table.
 */
void mm_defrag(struct mpool *ppool) *)
Definition mm_defrag (s : concrete_state) (ppool : mpool)
  : (concrete_state * mpool) :=
  (s, ppool). (* TODO *)
