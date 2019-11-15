Mailbox related APIs

api_fetch_waiter
  called by api_mailbox_waiter_get
    
spci_msg_recv_return
  called by called by api_vcpu_prepare_run
  called by api_spci_msg_recv
    
api_waiter_result
  called by api_mailbox_clear
  called by api_vm_configure
  
api_vm_configure_stage1
  called by api_vm_configure_pages
    called by api_vm_configure
    
msg_receiver_busy
  called by api_spci_msg_send

deliver_msg
  called by api_spci_msg_send

api_waiter_result

/* api_spci_msg_send */
/* api_spci_msg_recv */

************************
api_vm_configure
************************

TODO

************************
api_mailbox_writable_get
************************

Retrieves the next VM whose mailbox became writable.
??? How does it work exactly ???

api_mailbox_writable_get(current_vcpu) {
  if vm->mailbox.ready_list->is_empty()
     return -1
  entry = vm->mailbox.ready_list->pop() 
  return entry->vm_id
}

************************
api_mailbox_waiter_get
************************

api_mailbox_waiter_get(vm_id, current_vcpu) {
  if vm_id is not primary {
      return -1
  }
  vm = vm_find(vm_id)
  // Fetch VM entry waiting for the given vm.
  waiting_vm = api_fetch_waiter(vm)
  
  // There is no VM waiting for the give vm writable.
  if (waiting_vm == NULL) { return -1 }
  
  // Enqueue notification to waiting VM
  // If it is not "ready" already, make it "ready"
  // What does it do????
  if (entry is empty) {
      waiting_vm->mailbox->ready_list(waiting_vm)
  }
  
  // Return the ID of the waiting VM
  return waiting_vm->id
}

****************
api_mailbox_clear
****************

api_mailbox_clear(current_vcpu) {
  if empty return 0
  if received return -1
  if read {
    ret = api_waiter_result(vm)
    vm->mailbox.state = EMPTY
    return ret
  }
}

****************
Random Notes
****************

switch_to_primary : can we abstract it?
Why mailbox needs to be explicitly cleared instead of being implicitly cleared once read?
