use crate::mpool::*;
use crate::page::*;
use crate::types::*;

// To eliminate the risk of deadlocks, we define a partial order for the acquisition of locks held
// concurrently by the same physical CPU. Our current ordering requirements are as follows:
//
// vm::lock -> vcpu::lock
//
// Locks of the same kind require the lock of lowest address to be locked first, see
// `sl_lock_both()`.

// Currently, a page is mapped for the send and receive buffers so the maximum request is the size
// of a page.
const_assert_eq!(hf_mailbox_size; HF_MAILBOX_SIZE, PAGE_SIZE);

struct Api {
    mpool: MPool,
}

impl Api {
    /// Initialises the API page pool by taking ownership of the contents of the given page pool.
    pub fn new(mpool: &MPool) -> Self {
        Self {
            mpool: MPool::new_from(mpool),
        }
    }
}
