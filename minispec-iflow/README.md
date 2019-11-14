This is a small coq specification of a subset of Hafnium. For now, this spec is 
meant to be used to study a proposed security condition and is not meant to be 
totally accurate or complete. It is meant to model some of the more 
difficult/interesting aspects of formalizing security.

## How mailbox works 

**[NOTE]** It turns out that with a recent change in code, memory sharing request could be also done by sending a mailbox message to another VM. For now, let's ingore that aspect.

The following are relevant hypervisor calls.

* configure
* send
* recv
* release
* get_waiter
* get_writable
* **Anything other than these?**

How send/recv works when the target VM's mailbox is available.

1. The source VM calls `send()` to send a message to the target VM. The target VM's mailbox is EMPTY.
   The source VM's mailbox becomes RECEIVED. The send succeeds and the context switches to the primary VM
   so that it can allow the target VM to process the message. **[How doe it really work?]**
2. The target VM calls `recv()` to check if received a message. The target VM's mailbox becomes READ.
3. The target VM reads the recv buffer.
4. The target VM calls `rx_release()` to clear the message. The target VM's mailbox becomes EMPTY.

How send/recv works when the target VM's mailbox is busy and the source VM wants to be blocked.

1. The source VM calls `send()` to send a message to the target VM. The target VM's mailbox is busy.
   The send fails. The source VM is added in the waiter list of the target VM's mailbox.
2. The target VM reads the message in the mailbox and clear the mail box. The target VM's mailbox comes EMPTY.
3. The primary VM **somehow calls** `waiter_get()` to add the target VM in the ready list of the source VM.
   The primary VM **shomehow notifies** the source VM so that it can retry sending the message.
4. The source VM **somehow discovers** that one of the busy mailboxes become available. It retries sending the message.

## How waiting/ready list works

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

* When VM `a` wants to send a message to VM `b` but `b` is busy, `a->wait_entries[b->id]` gets added into `b->mailbox->waiter_list`. In the code, this happens in `msg_receiver_busy()`.
  
* When VM `b` becomes available later and wants to notify its availability to VM `a`, `a`'s wait_entry in `b->mailbox->waiter_list`, which is the same as `a->waiter_list[b->id]`, gets removed. Then, the removed entry gets added into `a->mailbox->ready_list`. In the code, this happens in `api_fetch_waiter()`.

* **[NEED CHECK]** Does the primary VM notify a VM to retry sending a message to another VM using vitural interrupts? Or, does it do something when scheduling a VM to run?
 
The ready list represents VMs that (1) the mailbox's owner tried to send messages but couldn't because their mailboxes were busy but then their mailboxes became available later. This does not mean that the mailboxes of the VMs are still availabl because they may have received new messages in between. Hafnium provides a hypervior call, available to all VMs, that removes and then returns an entry from the ready list given a VM's ID. The caller uses this hypervisor call to try sending the message to the VM of the returend ID.

* A VM can check if there has been any VM that notified its mailbox had become available by calling a HVC call, which eventually calls `api_mailbox_writable_get()`. In this function, the ID of the VM represented by an entry `entry` in `ready_list` can be constructed by computing `entry - a->wait_entries`.

## How to abstract waiting/ready list

Use VM's IDs instead of `wait_entry`. Then, `wating_list` and `ready_list` are just the lists of VM's IDs. 

One tricky thing is that, in `api_mailbox_waiter_get()`, it checks if a VM is already in the ready list to avoid adding it again. Well, in reality, when using intrusive list, it is impossible to add an entry multiple times. So, avoidance of redundant addition might be just a side effect.

In the top-level spec, we can achieve the same effect by checking the `ready_list`.

## Switching to the primary VM

Both `send()` and `recv()` could end with switching to the primary VM. For `send()`, it is to enable the receiving VM to process the received message as soon as possbile. For `recv()`, it is to block the sending VM until it receives the expected message. In both cases, when the VM resumes execution later, it will return from the corresponding hypervisor call with appropriate return values.
