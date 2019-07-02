Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Hafnium.Concrete.State.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Concrete.Notations.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.Constants.
Require Import Hafnium.Concrete.Assumptions.Mpool.
Require Import Hafnium.Concrete.MM.Implementation.

(*** This file transcribes necessary functions from mm.c, with the original C in
     comments alongside. ***)

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
           (vid : nat) (* named [vid] because [vm_id] is a field name in [vm] *)
           (addr : ipaddr_t)
           (size : size_t)
           (share : hf_share)
           (current : vm)
  (* returns success boolean and new state *)
  : bool * concrete_state :=

  (** first, we transcribe the goto locations so we can reuse them **)

  (*
    fail_return_to_sender:
	mm_vm_identity_map(&from->ptable, pa_begin, pa_end, orig_from_mode,
			   NULL, &local_page_pool);
     fail:
         ret = -1;
     out:
         sl_unlock(&from->lock);
         sl_unlock(&to->lock);
         mpool_fini(&local_page_pool);
         return ret;
   *)
  let goto_out :=
      (fun (state : concrete_state) (local_page_pool : mpool) (success : bool) =>
         match mpool_fini local_page_pool with
         | Some new_api_page_pool =>
           (* update api pool and return success + new state *)
           let state :=
               {|
                 ptable_lookup := state.(ptable_lookup);
                 api_page_pool := new_api_page_pool;
               |} in
           (success, state)
         | None => (success, state) (* this means there was no fallback pool *)
         end) in

  let goto_fail :=
      (fun (state : concrete_state) (local_page_pool : mpool) =>
         goto_out state local_page_pool false) in

  let goto_fail_return_to_sender :=
      (fun (state : concrete_state) (local_page_pool : mpool)
           (from : vm) (pa_begin pa_end : paddr_t) (orig_from_mode : mode_t) =>
         (* N.B. ignore the success boolean, as the code does *)
         let '(_, state, local_page_pool) :=
             mm_vm_identity_map state
                                (from.(vm_root_ptable))
                                pa_begin
                                pa_end
                                orig_from_mode
                                local_page_pool in
         goto_fail state local_page_pool) in

  (* struct vm *from = current->vm; *)
  let from := current in

  (*
    /* Disallow reflexive shares as this suggests an error in the VM. */
    if (vm_id == from->id) {
       return -1;
    }
   *)
  if (vid =? from.(vm_id))
  then (false, state)
  else
    (*
      /* Ensure the target VM exists. */
      to = vm_find(vm_id);
      if (to == NULL) {
              return -1;
      }
     *)
    match vm_find vid with
    | None => (false, state)
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
        | INVALID => (false, state)
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
          | (false, _) => goto_fail state local_page_pool
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
            then goto_fail state local_page_pool
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
              then goto_fail state local_page_pool (* first failure case *)
              else
                (* we have to handle the else-if case separately, checking
                   MM_MODE_UNOWNED again *)
                if (!(orig_from_mode & MM_MODE_UNOWNED)%N
                     && (orig_from_mode & MM_MODE_SHARED)%N)%bool
                then goto_fail state local_page_pool
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
                  | (false, new_state, new_local_page_pool) =>
                    goto_fail new_state new_local_page_pool
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
                    | (false, new_state, new_local_page_pool) =>
                      goto_fail_return_to_sender
                        new_state
                        new_local_page_pool
                        from
                        pa_begin
                        pa_end
                        orig_from_mode
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
                      | (false, state, local_page_pool) =>
                        let '(_, state, local_page_pool) :=
                            mm_vm_defrag state from.(vm_root_ptable) local_page_pool in
                        goto_fail_return_to_sender
                          new_state
                          new_local_page_pool
                          from
                          pa_begin
                          pa_end
                          orig_from_mode
                      | (true, new_state, new_local_page_pool) =>
                        let state := new_state in
                        let local_page_pool := new_local_page_pool in
                        (*
                                ret = 0;
                                goto out;
                         *)
                        let success := true in
                        goto_out state local_page_pool success
                      end
                    end
                  end
          end
        end
    end.
