# Scheduler VM expectations

Hafnium requires there to be a special 'primary' or 'scheduler' VM which is
responsible for scheduling the other VMs. There are some particular expectations
on this VM that are required for the rest of the system to function normally.

[TOC]

## Scheduling

The scheduler VM is responsible for scheduling the vCPUs of all the other VMs.
It should request information about the VMs in the system using the
`SPCI_PARTITION_INFO_GET` function, and then schedule their vCPUs as it wishes.
The recommended way of doing this is to create a kernel thread for each vCPU,
which will repeatedly run that vCPU by calling `SPCI_RUN`.

`SPCI_RUN` will return one of several possible functions, which must be handled
as follows:

### `SPCI_INTERRUPT`

The vCPU has been preempted but still has work to do. If the scheduling quantum
has not expired, the scheduler MUST call `hf_vcpu_run` on the vCPU to allow it
to continue.

### `SPCI_YIELD`

The vCPU has voluntarily yielded the CPU. The scheduler SHOULD take a scheduling
decision to give cycles to those that need them but MUST call `hf_vcpu_run` on
the vCPU at a later point.

### `SPCI_MSG_WAIT`

The vCPU is blocked waiting for a message. The scheduler MUST take it off the
run queue and not call `SPCI_RUN` on the vCPU until it has either:

*   injected an interrupt
*   sent it a message
*   received `HF_SPCI_RUN_WAKE_UP` for it from another vCPU
*   the timeout provided in `w2` is not `SPCI_SLEEP_INDEFINITE` and the
    specified duration has expired.

### `SPCI_MSG_SEND`

A message has been sent by the vCPU. If the recipient is the scheduler VM itself
then it can handle it as it pleases. Otherwise the scheduler MUST run a vCPU
from the recipient VM and priority SHOULD be given to those vCPUs that are
waiting for a message. The scheduler should call SPCI_RUN again on the sending
VM as usual.

### `SPCI_RX_RELEASE`

The vCPU has made the mailbox writable and there are pending waiters. The
scheduler MUST call `hf_mailbox_waiter_get()` repeatedly and notify all waiters
by injecting an `HF_MAILBOX_WRITABLE_INTID` interrupt. The scheduler should call
SPCI_RUN again on the sending VM as usual.

### `HF_SPCI_RUN_WAIT_FOR_INTERRUPT`

_This is a Hafnium-specific function not part of the SPCI standard._

The vCPU is blocked waiting for an interrupt. The scheduler MUST take it off the
run queue and not call `SPCI_RUN` on the vCPU until it has either:

*   injected an interrupt
*   received `HF_SPCI_RUN_WAKE_UP` for it from another vCPU
*   the timeout provided in `w2` is not `SPCI_SLEEP_INDEFINITE` and the
    specified duration has expired.

### `HF_SPCI_RUN_WAKE_UP`

_This is a Hafnium-specific function not part of the SPCI standard._

Hafnium would like `hf_vcpu_run` to be called on another vCPU, specified by
`hf_vcpu_run_return.wake_up`. The scheduler MUST either wake the vCPU in
question up if it is blocked, or preempt and re-run it if it is already running
somewhere. This gives Hafnium a chance to update any CPU state which might have
changed. The scheduler should call SPCI_RUN again on the sending VM as usual.

### `SPCI_ERROR`

#### `SPCI_ABORTED`

The vCPU has aborted triggering the whole VM to abort. The scheduler MUST treat
this the same as `HF_SPCI_RUN_WAKE_UP` for all the other vCPUs of the VM. For
this vCPU the scheduler SHOULD either never call SPCI_RUN on the vCPU again, or
treat it the same as `HF_SPCI_RUN_WAIT_FOR_INTERRUPT`.

#### Any other error code

This should not happen if the scheduler VM has called `SPCI_RUN` correctly, but
in case there is some other error it should be logged. The scheduler SHOULD
either try again or suspend the vCPU indefinitely.

## Interrupt handling

The scheduler VM is responsible for handling all hardware interrupts. Many of
these will be intended for the scheduler VM itself and it can handle them as
usual. However, it must also:

*   Enable, handle and ignore interrupts for the non-secure hypervisor physical
    timer (PPI 10, IRQ 26).
*   Forward interrupts intended for secondary VMs to an appropriate vCPU of the
    VM by calling `hf_interrupt_inject` and then running the vCPU as usual with
    `SPCI_RUN`. (If the vCPU is already running at the time that
    `hf_interrupt_inject` is called then it must be preempted and run again so
    that Hafnium can inject the interrupt.)
