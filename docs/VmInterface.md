# VM interface

This page provides an overview of the interface Hafnium provides to VMs. Hafnium
makes a distinction between the 'primary VM', which controls scheduling and has
more direct access to some hardware, and 'secondary VMs' which exist mostly to
provide services to the primary VM, and have a more paravirtualised interface.
The intention is that the primary VM can run a mostly unmodified operating
system (such as Linux) with the addition of a Hafnium driver, while secondary
VMs will run more specialised trusted OSes or bare-metal code which is designed
with Hafnium in mind.

The interface documented here is what is planned for the first release of
Hafnium, not necessarily what is currently implemented.

## CPU scheduling

The primary VM will have one vCPU for each physical CPU, and control the
scheduling.

Secondary VMs will have a configurable number of vCPUs, scheduled on arbitrary
physical CPUs at the whims of the primary VM scheduler.

All VMs will start with a single active vCPU. Subsequent vCPUs can be started
through PSCI.

## PSCI

The primary VM will be able to control the physical CPUs through the following
PSCI 1.1 calls, which will be forwarded to the underlying implementation in EL3:

*   PSCI_VERSION
*   PSCI_FEATURES
*   PSCI_SYSTEM_OFF
*   PSCI_SYSTEM_RESET
*   PSCI_AFFINITY_INFO
*   PSCI_CPU_SUSPEND
*   PSCI_CPU_OFF
*   PSCI_CPU_ON

All other PSCI calls are unsupported.

Secondary VMs will be able to control their vCPUs through the following PSCI 1.1
calls, which will be implemented by Hafnium:

*   PSCI_VERSION
*   PSCI_FEATURES
*   PSCI_AFFINITY_INFO
*   PSCI_CPU_SUSPEND
*   PSCI_CPU_OFF
*   PSCI_CPU_ON

All other PSCI calls are unsupported.

## Hardware timers

The primary VM will have access to both the physical and virtual EL1 timers
through the usual control registers (`CNT[PV]_TVAL_EL0` and `CNT[PV]_CTL_EL0`).

Secondary VMs will have access to the virtual timer only, which will be emulated
with help from the kernel driver in the primary VM.

## Interrupts

The primary VM will have direct access to control the physical GIC, and receive
all interrupts (other than anything already trapped by TrustZone). It will be
responsible for forwarding any necessary interrupts to secondary VMs. The
Interrupt Translation Service (ITS) will be disabled by Hafnium so that it
cannot be used to circumvent access controls.

Secondary VMs will have access to a simple paravirtualized interrupt controller
through two hypercalls: one to enable or disable a given virtual interrupt ID,
and one to get and acknowledge the next pending interrupt. There is no concept
of interrupt priorities or a distinction between edge and level triggered
interrupts. Secondary VMs may also inject interrupts into their own vCPUs.

## Performance counters

VMs will be blocked from accessing performance counter registers (for the
performance monitor extensions described in chapter D5 of the ARMv8-A reference
manual) in production, to prevent them from being used as a side channel to leak
data between VMs.

Hafnium may allow VMs to use them in debug builds.

## Debug registers

VMs will be blocked from accessing debug registers in production builds, to
prevent them from being used to circumvent access controls.

Hafnium may allow VMs to use these registers in debug builds.

## RAS Extension registers

VMs will be blocked from using registers associated with the RAS Extension.

## Asynchronous message passing

VMs will be able to send messages of up to 4 KiB to each other asynchronously,
with no queueing, as specified by SPCI.

## Memory

VMs will statically be given access to mutually-exclusive regions of the
physical address space at boot. This includes MMIO space for controlling
devices, plus a fixed amount of RAM for secondaries, and all remaining address
space to the primary. Note that this means that only one VM can control any
given page of MMIO registers for a device.

VMs may choose to donate or share their memory with other VMs at runtime. Any
given page may be shared with at most 2 VMs at once (including the original
owning VM). Memory which has been donated or shared may not be forcefully
reclaimed, but the VM with which it was shared may choose to return it.

## Logging

VMs may send a character to a shared log by means of a hypercall or SMC call.
These log messages will be buffered per VM to make complete lines, then output
to a Hafnium-owned UART and saved in a shared ring buffer which may be extracted
from RAM dumps. VM IDs will be prepended to these logs.

This log API is intended for use in early bringup and low-level debugging. No
sensitive data should be logged through it. Higher level logs can be sent to the
primary VM through the asynchronous message passing mechanism described above,
or through shared memory.

## Configuration

Hafnium will read configuration from a flattened device tree blob (FDT). This
may either be the same device tree used for the other details of the system or a
separate minimal one just for Hafnium. This will include at least:

*   The available RAM.
*   The number of secondary VMs, how many vCPUs each should have, how much
    memory to assign to each of them, and where to load their initial images.
    (Most likely the initial image will be a minimal loader supplied with
    Hafnium which will validate and load the rest of the image from the primary
    later on.)
*   Which devices exist on the system, their details (MMIO regions, interrupts
    and SYSMMU details), and which VM each is assigned to.
    *   A single physical device may be split into multiple logical ‘devices’
        from Hafnium’s point of view if necessary to have different VMs own
        different parts of it.
*   A whitelist of which SMC calls each VM is allowed to make.

## Failure handling

If a secondary VM tries to do something it shouldn't, Hafnium will either inject
a fault or kill it and inform the primary VM. The primary VM may choose to
restart the system or to continue without the secondary VM.

If the primary VM tries to do something it shouldn't, Hafnium will either inject
a fault or restart the system.

## TrustZone communication

The primary VM will be able to communicate with a TEE running in TrustZone
either through SPCI messages or through whitelisted SMC calls, and through
shared memory.

## Other SMC calls

Other than the PSCI calls described above and those used to communicate with
Hafnium, all other SMC calls will be blocked by default. Hafnium will allow SMC
calls to be whitelisted on a per-VM, per-function ID basis, as part of the
static configuration described above. These whitelisted SMC calls will be
forwarded to the EL3 handler with the client ID (as described by the SMCCC) set
to the calling VM's ID.
