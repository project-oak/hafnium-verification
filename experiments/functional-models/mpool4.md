// Merge with SpinLock module (final spec)
// SPINLOCK + MPOOL3 <= SPINLOCK + MPOOL4

Id: Type := Int64;
Page: Type := Int64;
Mpool: Type := { page_size: size_t, pages: Set<Page>, fallback: Id? }

Module MPOOL4 {
  manager: Id -> mpool?;

  fun new(page_size: size_t): Id {
    newId := manager.fresh_Id();
    manager[newId] := Some(Mpool { page_size, Set::empty(), None });
    newId
  }
 
  fun new_from(from: Id): Id {
    mpool_from := manager[from].get!();
    newId := new(mpool_from.page_size);
    manager[newId] := Some(mpool_from);
    manager[from] := None;
    newId
  }
  
  fun new_with_fallback(fallback: Id): Id {
    mpool_fallback := manager[from].get!();
    newId := new(mpool_fallback.page_size);
    manager[newId].fallback = Some(mpool_fallback);
    newId
  }
  
  fun fini(p: Id): unit {
    mpool := manager[p].get!();
    if(mpool.fallback == None) return;
    mpool_fallback := mpool.fallback.get!();
    mpool_fallback.pages += mpool.pages;
    manager[p] = None;
    ()
  }

  fun alloc(p: Id): Page {
    mpool = manager[p].get!();
    match mpool.pages.pop() with
    | Some page => return page
    | None =>
      match mpool.fallback with
      | Some next_id => alloc(next_id)
      | None => return NULL
      end
    end
    unreachable!();
  }

  fun free(p: Id, ptr: Page): unit {
    mpool := manager[p].get!();
    mpool.pages.push(ptr);
    ()
  }
/* TODO:
void *mpool_alloc_contiguous(struct mpool *p, size_t count, size_t align);
bool mpool_add_chunk(struct mpool *p, void *begin, size_t size);
void mpool_enable_locks(void);
*/
}
