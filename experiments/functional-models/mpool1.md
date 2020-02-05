//Concurrency Abstraction
//SimRel:

struct mpool {
  struct spinlock *lock;
  size_t entry_size;
  struct mpool_chunk *chunk_list;
  struct mpool_entry *entry_list;
  struct mpool *fallback;
};

Module Mpool {
  isRunning: (struct mpool*) -> bool?
  struct mpool *mpool_new(size_t entry_size) {
    (** UNCHANGED **)
  }
 
  void mpool_fini(struct mpool *p) { 
    CODE_A;
    [** sl_lock(p->lock) **];
    assert!(isRunning[p] == Some(false));
    isRunning[p] = Some(true);
    CODE_B;
    isRunning[p] = Some(false);
    [** sl_unlock(p->lock) **];
  }
  
  static void *mpool_alloc_no_fallback(struct mpool *p) { 
    CODE_A;
    [** sl_lock(p->lock) **];
    assert!(isRunning[p] == Some(false));
    isRunning[p] = Some(true);
    CODE_B;
    isRunning[p] = Some(false);
    [** sl_unlock(p->lock) **];
    CODE_C;
  }
 
  void *mpool_alloc(struct mpool *p) {
    (** UNCHANGED **)
  }
 
  void mpool_free(struct mpool *p, void *ptr) { 
    CODE_A;
    [** sl_lock(p->lock) **];
    assert!(isRunning[p] == Some(false));
    isRunning[p] = Some(true);
    CODE_B;
    isRunning[p] = Some(false);
    [** sl_unlock(p->lock) **];
  }
}
