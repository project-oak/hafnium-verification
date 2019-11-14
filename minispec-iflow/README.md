This is a small coq specification of a subset of Hafnium. For now, this spec is 
meant to be used to study a proposed security condition and is not meant to be 
totally accurate or complete. It is meant to model some of the more 
difficult/interesting aspects of formalizing security.

## How waiting/ready list in VM's mailbox works

In Hafnium, a VM struct has a field called `mailbox` that maintains its waiter list and ready list. 

~~~
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
~~~

The waiter list represents VMs that tried to send message to the mailbox owner but couldn't because the mailbox was busy at that time. Hafnium provides a hypervisor call, accessible only by the primary VM, that removes and then returns an entry from the waiter list given a VM's ID. The primary VM uses this hypervisor call to schedule a VM so that it can try sending the message again. 

The ready list represents VMs that (1) the mailbox's owner tried to send messages but couldn't because their mailboxes were busy but then their mailboxes became available later. This does not mean that the mailboxes of the VMs are still availabl because they may have received new messages in between. Hafnium provides a hypervior call, available to all VMs, that removes and then returns an entry from the ready list given a VM's ID. The caller uses this hypervisor call to try sending the message to the VM of the returend ID.

When VM `a` wants to send a message to VM `b` but `b` is busy, `a->wait_entries[b->id]` gets added into `b->mailbox->waiter_list`. In the code, this happens in `msg_receiver_busy()`.
  
When VM `b` becomes available later and wants to notify its availability to VM `a`, `a`'s wait_entry in `b->mailbox->waiter_list`, which is the same as `a->waiter_list[b->id]`, gets removed. Then, the removed entry gets added into `a->mailbox->ready_list`. In the code, this happens in `api_fetch_waiter()`.

A VM can check if there has been any VM that notified its mailbox had become available by calling a HVC call, which eventually calls `api_mailbox_writable_get()`. In this function, the ID of the VM represented by an entry `entry` in `ready_list` can be constructed by computing `entry - a->wait_entries`.

## How waiting/ready list could be abstracted in the top-level specification

Use VM's IDs instead of `wait_entry`. Then, `wating_list` and `ready_list` are just the lists of VM's IDs. 

One tricky thing is that, in `api_mailbox_waiter_get()`, it checks if a VM is already in the ready list to avoid adding it again. Well, in reality, when using intrusive list, it is impossible to add an entry multiple times. So, avoidance of redundant addition might be just a side effect.

In the top-level spec, we can achieve the same effect by checking the `ready_list`.
