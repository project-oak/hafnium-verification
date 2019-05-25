use core::mem;
use core::cell::UnsafeCell;

use crate::types::*;
use crate::spinlock::*;

// Virtual CPU's state.
#[repr(C)]
enum VcpuState {
    /// The vcpu is switched off,
    Off,

    /// The vcpu is ready to be run.
	  Ready,

    /// The vcpu is currently running.
	  Running,

    /// The vcpu is waiting for a message.
	  BlockedMailbox,

    /// The vcpu is waiting for an interrupt.
	  BlockedInterrupt,

	  /// The vcpu has aborted.
    Aborted,
}

/// Type of registers that hold interrupt status.
type InterruptRegisterType = u32;
const INTERRUPT_REGISTER_BITS: usize = 8 * mem::size_of::<InterruptRegisterType>();
const_assert!(interrupt_register_bits; HF_NUM_INTIDS % INTERRUPT_REGISTER_BITS == 0);

#[repr(C)]
struct Interrupts {
	  /// Bitfield keeping track of which interrupts are enabled.
    enabled: [InterruptRegisterType; HF_NUM_INTIDS / INTERRUPT_REGISTER_BITS],
    
	  /// Bitfield keeping track of which interrupts are pending.
    pending: [InterruptRegisterType; HF_NUM_INTIDS / INTERRUPT_REGISTER_BITS],

	  /// The number of interrupts which are currently both enabled and pending. i.e. the number of
	  /// bits set in interrupt_enable & interrupt_pending.
    enabled_and_pending_count: InterruptRegisterType,
}


#[repr(C)]
struct VcpuFaultInfo {
    ipaddr: usize,
    vaddr: usize,
    pc: usize,
    mode: c_int,
}

#[repr(C)]
struct VcpuInner {
    state: VcpuState,
    regs: ArchRegs,
}

#[repr(C)]
struct Vcpu {
    vm: &'static Vm,
    cpu: UnsafeCell<Option<CpuHandle>>,
    inner: SpinLock<VcpuInner>,
    interrupts: SpinLock<Interrupts>,
}

#[repr(C)]
struct CpuHandle {
    // TODO
}

#[repr(C)]
struct Vm {
    // TODO
}

#[repr(C)]
struct ArchRegs {
    // TODO
}
