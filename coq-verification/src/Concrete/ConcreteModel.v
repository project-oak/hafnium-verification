Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Hafnium.AbstractModel.
Import ListNotations.

(*** Low-level model : describes the concrete state of the Hafnium system ***)

Section Concrete.
  Context {ptable_pointer : Type}.

  Context {PAGE_SIZE : nat}.

  (* memory modes *)
  (* Note : mode flags are taken as *indices* in the binary number*) 
  Context (MM_MODE_R MM_MODE_W MM_MODE_X : N)
          (MM_MODE_INVALID MM_MODE_UNOWNED MM_MODE_SHARED : N).

  (* boilerplate : nicer display of memory mode operations *)
  Local Notation mode := N.
  Local Notation "[ x | .. | y ]" :=
    (N.setbit .. (N.setbit 0 x) .. y)
      (at level 49, y at level 0, only parsing) : N_scope.
  Local Notation "x & y " := 
    (N.testbit x y)
      (at level 49, y at level 0, only parsing) : N_scope.

  (* leave page attributes abstract to avoid assumptions about implementation *)
  Context {attributes : Type}
          {invalid : attributes -> bool}
          {unowned : attributes -> bool}
          {shared  : attributes -> bool}.
  Context {attrs_to_mode : attributes -> N}.
  Context {empty_attributes : attributes}
          {set_invalid : attributes -> attributes}
          {set_unowned : attributes -> attributes}
          {set_shared : attributes -> attributes}
          {set_RWX : attributes -> attributes}.
  Context {absent_attributes : attributes}
          {absent_attributes_invalid : invalid absent_attributes = true}.

  (* TODO: add fallback? *)
  (* TODO: make abstract? *)
  Definition mpool := list ptable_pointer.
  Definition mpool_alloc (mp : mpool) : option (mpool * ptable_pointer) :=
    match mp with
    | nil => None
    | ptr :: mp' => Some (mp', ptr)
    end.
  Definition mpool_free (mp : mpool) ptr : mpool := ptr :: mp.

  (* the way we have constructed mpools, they always allocate the most recently
     freed memory  anyway, fallbacks don't need special treatment. *)
  Definition mpool_init_with_fallback (fallback : mpool) := fallback.

  (* page table entry -- can be absent, table, or block *)
  Inductive pte : Type :=
  | AbsentPTE : pte
  | TablePTE : forall (next : ptable_pointer), pte
  | BlockPTE : forall (attrs : attributes), pte
  .

  Definition page_table := list pte. (* TODO : fix size *)

  Record vm :=
    {
      vm_root_ptable : ptable_pointer;
      id : nat;
    }.

  (* starting parameters -- don't change *)
  Class concrete_params :=
    {
      vms : list vm;
      hafnium_root_ptable : ptable_pointer;
    }.

  Record concrete_state :=
    {
      (* representation of the state of page tables in memory *)
      ptable_lookup : ptable_pointer -> page_table;
      api_page_pool : mpool;
    }.

  (* the part of a physical address that relates to page tables*)
  Record page_addr :=
    {
      lvl0_index : nat; (* index in root page table *)
      lvl1_index : nat; (* index in level-1 page table *)
      lvl2_index : nat; (* index in level-2 page table *)
      lvl3_index : nat; (* index in level-3 page table *)
    }.

  Definition get_index (lvl : nat) (a : page_addr) : nat :=
    match lvl with
    | 0 => a.(lvl0_index)
    | 1 => a.(lvl1_index)
    | 2 => a.(lvl2_index)
    | 3 => a.(lvl3_index)
    | _ => 0 (* invalid level *)
    end.

  Definition get_entry (ptable : page_table) (i : nat) : pte :=
    nth_default AbsentPTE ptable i.
  
  (* physical address: page address + offset in page table *)
  (* TODO: explain the "physical address" terminology *)
  Record physical_addr :=
    {
      pa_page : page_addr;
      pa_offset : nat;
    }.

  Axiom ipaddr : Type. (* intermediate physical address *)
  Axiom ipa_add : ipaddr -> nat -> ipaddr.
  Axiom ipa_addr : ipaddr -> nat. (* absolute address *)
  Axiom pa_from_ipa : ipaddr -> physical_addr.

  Fixpoint page_lookup'
           (s : concrete_state)
           (a : page_addr)
           (ptr : ptable_pointer)
           (* encode the level as (4 - level), so Coq knows this terminates *)
           (lvls_to_go : nat)
    : pte :=
    match lvls_to_go with
    | 0 => AbsentPTE
    | S lvls_to_go' =>
      let lvl := 4 - lvls_to_go in
      let ptable := s.(ptable_lookup) ptr in
      match (get_entry ptable (get_index lvl a)) with
      | TablePTE next_ptr => page_lookup' s a next_ptr lvls_to_go'
      | x => x
      end
    end.

  (* TODO: is this an API function? *)
  Definition vm_page_lookup
             (s : concrete_state) (v : vm) (a : page_addr) : pte :=
    page_lookup' s a v.(vm_root_ptable) 4.
  Definition hafnium_page_lookup
             {cp : concrete_params}
             (s : concrete_state)
             (a : page_addr) : pte :=
    page_lookup' s a hafnium_root_ptable 4.

  Definition get_attrs (e : pte) : attributes :=
    match e with
    | BlockPTE attrs => attrs
    | AbsentPTE => absent_attributes
    | TablePTE _ =>
      (* shouldn't get here; can't get attributes from a table *)
      absent_attributes
    end.
  

  (* TODO: move to AbstractModel *)
  Arguments owned_by {_} {_} _.
  Arguments accessible_by {_} {_} _.
  Definition abstract_state_equiv
             (s1 s2 : @abstract_state page_addr nat) : Prop :=
    (forall a, s1.(owned_by) a = s2.(owned_by) a)
    /\ (forall e a,
           In e (s1.(accessible_by) a) <-> In e (s2.(accessible_by) a)).

  (* for every API function, we need to prove that if the concrete state (is
     itself valid and) represents a valid abstract state before the call, then
     the concrete state after the call (is also valid and) represents a valid
     abstract state *)

  Definition vm_find {cp : concrete_params} (vid : nat) : option vm :=
    nth_error vms vid.

  Definition is_valid {cp : concrete_params} (s : concrete_state) : Prop :=
    (* Possible constraints:
          - Block PTEs have the valid bit set
          - page tables have a constant size
          - page table indices are always below page table size
          - vm_id corresponds to a VM's place in the vms list
     *)
    True.

  Definition represents
             {cp : concrete_params}
             (abst : @abstract_state page_addr nat)
             (conc : concrete_state) : Prop :=
    is_valid conc
    /\ (forall (vid : nat) (a : page_addr),
        In (inl vid) (abst.(accessible_by) a) <->
           (exists v : vm,
               vm_find vid = Some v
               /\ invalid (get_attrs (conc.(vm_page_lookup) v a)) = false))
    /\ (forall (a : page_addr),
           In (inr hid) (abst.(accessible_by) a) <->
           (invalid (get_attrs (conc.(hafnium_page_lookup) a)) = false))
    /\ (forall (vid : nat) (a : page_addr),
           abst.(owned_by) a = inl vid <->
           (exists v : vm,
               vm_find vid = Some v
               /\ unowned (get_attrs (conc.(vm_page_lookup) v a)) = false))
    /\ (forall (a : page_addr),
           abst.(owned_by) a = inr hid <->
           (unowned (get_attrs (conc.(hafnium_page_lookup) a)) = false))
  .

  (* hf_share enum *)
  Inductive hf_share :=
  | HF_MEMORY_GIVE
  | HF_MEMORY_LEND
  | HF_MEMORY_SHARE
  | INVALID
  .

  Definition is_aligned (absolute_addr page_size : nat ) :=
    absolute_addr mod page_size =? 0.

  (*
    static ptable_addr_t mm_round_down_to_page(ptable_addr_t addr)
    *)
  Definition mm_round_down_to_page (addr : physical_addr) : physical_addr :=
    {|
      pa_page := addr.(pa_page);
      pa_offset := 0;
    |}.

  Definition page_addr_to_int (a : page_addr) : nat :=
    fold_right
      (fun lvl out =>
         out + (get_index lvl a) * (PAGE_SIZE ^ (3 - lvl)))
      0 (seq 0 4).

  Definition int_to_page_addr (n : nat) : page_addr :=
    {|
      lvl0_index := (n / PAGE_SIZE ^ 3);
      lvl1_index := (n / PAGE_SIZE ^ 2) mod PAGE_SIZE;
      lvl2_index := (n / PAGE_SIZE) mod PAGE_SIZE;
      lvl3_index := n mod PAGE_SIZE;
    |}.

  (*
    static ptable_addr_t mm_round_up_to_page(ptable_addr_t addr)
    *)
  Definition mm_round_up_to_page (addr : physical_addr) : physical_addr :=
    {|
      pa_page := int_to_page_addr (page_addr_to_int (addr.(pa_page)) + 1);
      pa_offset := 0;
    |}.

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
  (* N.B. instead of operating on a passed-in reference and returning a boolean
     saying whether it's valid, we will instead return an [option] type. *)
  (* N.B. instead of passing in a page table we pass in the vm whose root table
     we are searching *)
  Definition mm_vm_get_attrs
             (s : concrete_state)
             (t : ptable_pointer)
             (begin end_ : physical_addr) : option mode :=
    None. (* TODO *)
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
  (* N.B. instead of operating on a passed-in reference and returning a boolean
     saying whether it's valid, we will instead return an [option] type. *)
  Definition mm_vm_get_mode
             (s : concrete_state)
             (t : ptable_pointer)
             (begin end_ : ipaddr) : option mode :=
    None. (* TODO *)

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
             (begin : physical_addr)
             (end_ : physical_addr)
             (mode : mode)
             (ppool : mpool) : option (concrete_state * mpool) :=
    None. (* TODO *)

  Definition mpool_fini (s : concrete_state) (ppool : mpool)
    : concrete_state := s. (* TODO *)

  
  Local Notation "! x" := (negb x) (at level 100) : bool_scope.

  (*
    /**
    * Clears a region of physical memory by overwriting it with zeros. The data is
    * flushed from the cache so the memory has been cleared across the system.
    */
    static bool api_clear_memory(paddr_t begin, paddr_t end, struct mpool *ppool)
   *)
  Definition api_clear_memory
             (s : concrete_state)
             (begin : physical_addr)
             (end_ : physical_addr)
             (ppool : mpool) : option (concrete_state * mpool) :=

    None. (* TODO *)

  (*
  int64_t api_share_memory(spci_vm_id_t vm_id, ipaddr_t addr, size_t size,
                         enum hf_share share, struct vcpu *current)
  *)
  Definition api_share_memory
             {cp : concrete_params}
             (state : concrete_state)
             (vm_id : nat)
             (addr : ipaddr)
             (size : nat)
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
                 ( MM_MODE_INVALID,
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
            | None => FAIL
            | Some orig_from_mode =>
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
                              | None => false
                              | Some orig_to_mode =>
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
                    | None => FAIL
                    | Some (new_state, new_local_page_pool) =>
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
                      | None => FAIL
                      | Some (new_state, new_local_page_pool) =>
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
                        | None =>
                          (* TODO: the function needs to return some
                          state even if it fails, and we need to do
                          the defrag here and do the other extra
                          remapping steps in other failure cases. *)
                          FAIL
                      | Some (new_state, new_local_page_pool) =>
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
  (* TODO: fix option functions so they always change the state and do return a bool *)
  (* TODO: separate different parts (mm, mpool, api, etc) into different files *)
