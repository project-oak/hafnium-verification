/*
 * Copyright 2019 Jeehoon Kang
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

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
