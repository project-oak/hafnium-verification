This is a small coq specification of a subset of Hafnium. For now, this spec is 
meant to be used to study a proposed security condition and is not meant to be 
totally accurate or complete. It is meant to model some of the more 
difficult/interesting aspects of formalizing security.

How waiting/ready list in VM's mailbox works.

mailbox {
  :
  list_entry waiter_list
  list_entry ready_list
}

vm {
  :
  mailbox mailbox
  wait_entry wait_entries[MAX_VMS]
}

When VM a wants to send a message to VM b but VM b is busy
  a->wait_entries[b->id] gets added into b->mailbox->waiter_list
  
When VM b becomes available and wants to notify its availability to VM a
  a's wait_entry in b->mailbox->waiter_list (= a->waiter_list[b->id]) gets removed
     => The removed entry is a->wait_entries[b->id]]
  Then, then the removed entry gets added into a->mailbox->ready_list
     => In the ready_list, the ID of the target VM represented by the entry can be
        found by computing entry - a->wait_entries
