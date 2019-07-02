Require Import Coq.NArith.BinNat.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Notations.
Require Import Hafnium.Concrete.State.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.Constants.
Require Import Hafnium.Concrete.Assumptions.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Mpool.

(*** This file transcribes necessary functions from mm.c, with the original C in
     comments alongside. ***)

(* typedef uintvaddr_t ptable_addr_t; *)
Definition ptable_addr_t : Type := uintvaddr_t.
Bind Scope N_scope with ptable_addr_t.

(* static ptable_addr_t mm_round_down_to_page(ptable_addr_t addr) *)
Definition mm_round_down_to_page (addr : ptable_addr_t) : ptable_addr_t :=
  (* return addr & ~((ptable_addr_t)(PAGE_SIZE - 1)); *)
   N.land addr (N.lnot (PAGE_SIZE - 1) (N.size addr)).

(* static ptable_addr_t mm_round_up_to_page(ptable_addr_t addr) *)
Definition mm_round_up_to_page (addr : ptable_addr_t) : ptable_addr_t :=
  (* return mm_round_down_to_page(addr + PAGE_SIZE - 1); *)
  mm_round_down_to_page (addr + PAGE_SIZE - 1).

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
                              ptable_addr_t end, uint64_t *attrs)
 *)
(* N.B. instead of passing in a page table we pass in the vm whose root table
   we are searching *)
Definition mm_vm_get_attrs
           (s : concrete_state)
           (t : ptable_pointer)
           (begin end_ : ptable_addr_t) : bool * attributes :=
  (false, 0%N). (* TODO *)
(*
  /**
  * Gets the mode of the give range of intermediate physical addresses if they
  * are mapped with the same mode.
  *
  * Returns true if the range is mapped with the same mode and false otherwise.
  */
  bool mm_vm_get_mode(struct mm_ptable *t, ipaddr_t begin, ipaddr_t end,
       int *mode)
 *)
(* N.B. the comment above the function means "the entire range of addresses
   has one consistent mode" and not "the range of addresses has the same
   mode as is indicated by the pointer passed in". *)
Definition mm_vm_get_mode
           (s : concrete_state)
           (t : ptable_pointer)
           (begin end_ : ipaddr_t) : bool * mode_t :=
  (false, 0%N). (* TODO *)

(*
  /**
  * Updates a VM's page table such that the given physical address range is
  * mapped in the address space at the corresponding address range in the
  * architecture-agnostic mode provided.
  */
  bool mm_vm_identity_map(struct mm_ptable *t, paddr_t begin, paddr_t end,
                          int mode, ipaddr_t *ipa, struct mpool *ppool)
 *)
(* N.B. for now, ignoring the ipa argument, which is set to NULL in all calls
   I've found so far. *)
Definition mm_vm_identity_map
           (s : concrete_state)
           (t : ptable_pointer)
           (begin : paddr_t)
           (end_ : paddr_t)
           (mode : mode_t)
           (ppool : mpool) : (bool * concrete_state * mpool) :=
  (false, s, ppool).

(*
  /**
   * Defragments the VM page table.
   */
  void mm_vm_defrag(struct mm_ptable *t, struct mpool *ppool)
  *)
Definition mm_vm_defrag
           (s : concrete_state) (t : ptable_pointer) (ppool : mpool)
  : (bool * concrete_state * mpool) :=
  (false, s, ppool). (* TODO *)

(*
  /**
  * Updates the hypervisor page table such that the given physical address range
  * is mapped into the address space at the corresponding address range in the
  * architecture-agnostic mode provided.
  */
  void *mm_identity_map(paddr_t begin, paddr_t end, int mode, struct mpool *ppool)
 *)
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
  bool mm_unmap(paddr_t begin, paddr_t end, struct mpool *ppool)
 *)
Definition mm_unmap (s : concrete_state) (begin end_ : paddr_t) (ppool : mpool)
  : (bool * concrete_state * mpool) :=
  (false, s, ppool). (* TODO *)

(*
/**
 * Defragments the hypervisor page table.
 */
void mm_defrag(struct mpool *ppool)
 *)
Definition mm_defrag (s : concrete_state) (ppool : mpool)
  : (concrete_state * mpool) :=
  (s, ppool). (* TODO *)

(* TODO: deindent the C code in this file *)
