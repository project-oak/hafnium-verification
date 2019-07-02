Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Hafnium.AbstractModel.
Require Import Hafnium.Concrete.State.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Notations.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.Constants.
Require Import Hafnium.Concrete.Assumptions.Datatypes.
Require Import Hafnium.Concrete.Assumptions.Mpool.
Import ListNotations.

(*** Low-level model : describes the concrete state of the Hafnium system ***)

Section Concrete.

  Definition ptable_addr_t : Type := uintvaddr_t.
  Bind Scope N_scope with ptable_addr_t.

  (*
    static ptable_addr_t mm_round_down_to_page(ptable_addr_t addr)
    *)
  Definition mm_round_down_to_page (addr : ptable_addr_t) : ptable_addr_t :=
    (* return addr & ~((ptable_addr_t)(PAGE_SIZE - 1)); *)
     N.land addr (N.lnot (PAGE_SIZE - 1) (N.size addr)).

  (*
    static ptable_addr_t mm_round_up_to_page(ptable_addr_t addr)
    *)
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

  Definition mpool_fini (s : concrete_state) (ppool : mpool)
    : concrete_state := s. (* TODO *)

  (*
    /**
    * Clears a region of physical memory by overwriting it with zeros. The data is
    * flushed from the cache so the memory has been cleared across the system.
    */
    static bool api_clear_memory(paddr_t begin, paddr_t end, struct mpool *ppool)
   *)
  Definition api_clear_memory
             (s : concrete_state)
             (begin : paddr_t)
             (end_ : paddr_t)
             (ppool : mpool) : bool * concrete_state * mpool :=
    (false, s, ppool). (* TODO *)

  (*
  int64_t api_share_memory(spci_vm_id_t vm_id, ipaddr_t addr, size_t size,
                         enum hf_share share, struct vcpu *current)
  *)
  Definition api_share_memory
             {cp : concrete_params}
             (state : concrete_state)
             (vm_id : nat)
             (addr : ipaddr_t)
             (size : size_t)
             (share : hf_share)
             (current : vm)
    (* returns success boolean and new state *)
    : bool * concrete_state :=

    let FAIL := (false, state) in (* on failure, return "false" for success and old state *)
    
    (* struct vm *from = current->vm; *)
    let from := current in

    (*
      /* Disallow reflexive shares as this suggests an error in the VM. */
      if (vm_id == from->id) {
         return -1;
      }
    *)
    if (vm_id =? from.(id))
    then FAIL
    else
      (*
        /* Ensure the target VM exists. */
        to = vm_find(vm_id);
        if (to == NULL) {
                return -1;
        }
       *)
      match vm_find vm_id with
      | None => FAIL
      | Some to =>
  
        (*
          begin = addr;
          end = ipa_add(addr, size);
         *)
        let begin := addr in
        let end_ := ipa_add addr size in
        (*
          /* Fail if addresses are not page-aligned. */
          if (!is_aligned(ipa_addr(begin), PAGE_SIZE) ||
              !is_aligned(ipa_addr(end), PAGE_SIZE)) {
                  return -1;
          }
        *)
        if (!is_aligned (ipa_addr begin) PAGE_SIZE
            || !is_aligned (ipa_addr end_) PAGE_SIZE)%bool
        then (false, state)
        else
          (*
            /* Convert the sharing request to memory management modes. */
            switch (share) {
            case HF_MEMORY_GIVE:
                    from_mode = MM_MODE_INVALID | MM_MODE_UNOWNED;
                    to_mode = MM_MODE_R | MM_MODE_W | MM_MODE_X;
                    break;
            case HF_MEMORY_LEND:
                    from_mode = MM_MODE_INVALID;
                    to_mode = MM_MODE_R | MM_MODE_W | MM_MODE_X | MM_MODE_UNOWNED;
                    break;
            case HF_MEMORY_SHARE:
                    from_mode = MM_MODE_R | MM_MODE_W | MM_MODE_X | MM_MODE_SHARED;
                    to_mode = MM_MODE_R | MM_MODE_W | MM_MODE_X | MM_MODE_UNOWNED |
                              MM_MODE_SHARED;
                    break;
            default:
                    /* The input is untrusted so might not be a valid value. */
                    return -1;
            }
           *)
          let '(from_mode, to_mode) :=
              (match share with
               | HF_MEMORY_GIVE =>
                 ([ MM_MODE_INVALID | MM_MODE_UNOWNED ],
                 [ MM_MODE_R | MM_MODE_W | MM_MODE_X])%N
              | HF_MEMORY_LEND =>
                 ( [ MM_MODE_INVALID ],
                 [ MM_MODE_R | MM_MODE_W | MM_MODE_X | MM_MODE_UNOWNED ])%N
              | HF_MEMORY_SHARE =>
                 ([ MM_MODE_R | MM_MODE_W | MM_MODE_X | MM_MODE_SHARED ],
                 [ MM_MODE_R | MM_MODE_W | MM_MODE_X | MM_MODE_UNOWNED | MM_MODE_SHARED ])%N
              | INVALID =>
                (* unlike in the reference code, we need to return garbage here rather than
                   returning, and can protect ourselves by checking if [share] was invalid
                   before continuing *)
                (0, 0)%N
              end) in
          match share with
          | INVALID => FAIL
          | _ =>
            (*
              /*
               * Create a local pool so any freed memory can't be used by another
               * thread. This is to ensure the original mapping can be restored if any
               * stage of the process fails.
               */
              mpool_init_with_fallback(&local_page_pool, &api_page_pool);
              sl_lock_both(&from->lock, &to->lock);
             *)
            let local_page_pool := mpool_init_with_fallback state.(api_page_pool) in
            
            (*
              /*
               * Ensure that the memory range is mapped with the same mode so that
               * changes can be reverted if the process fails.
               */
              if (!mm_vm_get_mode(&from->ptable, begin, end, &orig_from_mode)) {
                      goto fail;
             }
             *)
            match mm_vm_get_mode state from.(vm_root_ptable) begin end_ with
            | (false, _) => FAIL
            | (true, orig_from_mode) =>
              (*
                /*
                * Ensure the memory range is valid for the sender. If it isn't, the
                * sender has either shared it with another VM already or has no claim
                * to the memory.
                */
                if (orig_from_mode & MM_MODE_INVALID) {
                        goto fail;
                }
               *)
              if (orig_from_mode & MM_MODE_INVALID)%N
              then FAIL
              else
                (*
                  /*
                  * The sender must own the memory and have exclusive access to it in
                  * order to share it. Alternatively, it is giving memory back to the
                  * owning VM.
                  */
                  if (orig_from_mode & MM_MODE_UNOWNED) {
                          int orig_to_mode;
                          if (share != HF_MEMORY_GIVE ||
                              !mm_vm_get_mode(&to->ptable, begin, end, &orig_to_mode) ||
                              orig_to_mode & MM_MODE_UNOWNED) {
                                  goto fail;
                          }
                  } else if (orig_from_mode & MM_MODE_SHARED) {
                          goto fail;
                  }
                 *)
                (* N.B. the case structure looks a little different here
                   because of functional/imperative differences -- each failure
                   case is handled as one big boolean *)
                if (((orig_from_mode & MM_MODE_UNOWNED)%N)
                      && ((match share with
                           | HF_MEMORY_GIVE => false
                           | _ => true
                           end)
                          || (match mm_vm_get_mode
                                      state to.(vm_root_ptable) begin end_ with
                              | (false, _) => false
                              | (true, orig_to_mode) =>
                                (orig_to_mode & MM_MODE_UNOWNED)%N
                              end)))%bool
                then FAIL (* first failure case *)
                else
                  (* we have to handle the else-if case separately, checking
                     MM_MODE_UNOWNED again *)
                  if (!(orig_from_mode & MM_MODE_UNOWNED)%N
                       && (orig_from_mode & MM_MODE_SHARED)%N)%bool
                  then FAIL
                  else
                    (*
                      pa_begin = pa_from_ipa(begin);
                      pa_end = pa_from_ipa(end);
                     *)
                    let pa_begin := pa_from_ipa begin in
                    let pa_end := pa_from_ipa end_ in

                    (*
                      /*
                      * First update the mapping for the sender so there is not overlap with
                      * the recipient.
                      */
                      if (!mm_vm_identity_map(&from->ptable, pa_begin, pa_end, from_mode,
                                              NULL, &local_page_pool)) {
                              goto fail;
                      }
                     *)
                    match mm_vm_identity_map state
                                             (from.(vm_root_ptable))
                                             pa_begin
                                             pa_end
                                             from_mode
                                             local_page_pool with
                    | (false, new_state, new_local_page_pool) => FAIL
                    | (true, new_state, new_local_page_pool) =>
                      let state := new_state in
                      let local_page_pool := new_local_page_pool in
                      (*
                      /* Clear the memory so no VM or device can see the previous contents. */
                      if (!api_clear_memory(pa_begin, pa_end, &local_page_pool)) {
                              goto fail_return_to_sender;
                      }
                       *)
                      match api_clear_memory state
                                             pa_begin
                                             pa_end
                                             local_page_pool with
                      | (false, new_state, new_local_page_pool) => FAIL
                      | (true, new_state, new_local_page_pool) =>
                        let state := new_state in
                        let local_page_pool := new_local_page_pool in
                        
                        (*
                        /* Complete the transfer by mapping the memory into the recipient. */
                        if (!mm_vm_identity_map(&to->ptable, pa_begin, pa_end, to_mode, NULL,
                                                &local_page_pool)) {
                                /* TODO: partial defrag of failed range. */
                                /* Recover any memory consumed in failed mapping. */
                                mm_vm_defrag(&from->ptable, &local_page_pool);
                                goto fail_return_to_sender;
                        }
                         *)
                        match mm_vm_identity_map state
                                                 (to.(vm_root_ptable))
                                                 pa_begin
                                                 pa_end
                                                 to_mode
                                                 local_page_pool with
                        | (false, new_state, new_local_page_pool) =>
                          (* TODO: the function needs to return some
                          state even if it fails, and we need to do
                          the defrag here and do the other extra
                          remapping steps in other failure cases. *)
                          FAIL
                        | (true, new_state, new_local_page_pool) =>
                          let state := new_state in
                        let local_page_pool := new_local_page_pool in
                        (*
                                  ret = 0;
                                  goto out;
                          out:
                                  sl_unlock(&from->lock);
                                  sl_unlock(&to->lock);
                                  mpool_fini(&local_page_pool);
                                  return ret;
                         *)
                        let state := mpool_fini state local_page_pool in
                        (true, state)
                        end
                      end
                    end
              
            end
          end
  end.

End Concrete.

  (* TODO: fix failure cases *)
  (* TODO: nicer way of failing? *)
  (* TODO: separate different parts (mm, mpool, api, etc) into different files *)
