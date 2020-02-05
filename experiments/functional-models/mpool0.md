[** EVERY LINE HAS YIELD BUT OMITTED **]

struct mpool {
  struct spinlock *lock;                     // <----- Δ with HAFNIUM
  size_t entry_size;
  struct mpool_chunk *chunk_list;
  struct mpool_entry *entry_list;
  struct mpool *fallback;
};

Module MPOOL0 {
  struct mpool *new(size_t entry_size) {     // <----- Δ with HAFNIUM
    struct mpool *p = malloc(sizeof(mpool)); // <----- Δ with HAFNIUM
    p->entry_size = entry_size;
    p->chunk_list = NULL;
    p->entry_list = NULL;
    p->fallback = NULL;
    p->lock = lock_new();                    // <----- Δ with HAFNIUM
    return p;                                // <----- Δ with HAFNIUM
  }
 
 
 
  void fini(struct mpool *p) {
	struct mpool_entry *entry;
	struct mpool_chunk *chunk;

    if (!p->fallback) {
        return;
    }

    lock(p);

    entry = p->entry_list;
    while (entry != NULL) {
        void *ptr = entry;

        entry = entry->next;
        free(p->fallback, ptr);
    }

    chunk = p->chunk_list;
    while (chunk != NULL) {
        void *ptr = chunk;
        size_t size = (uintptr_t)chunk->limit - (uintptr_t)chunk;

        chunk = chunk->next_chunk;
        add_chunk(p->fallback, ptr, size);
    }

    p->chunk_list = NULL;
    p->entry_list = NULL;
    p->fallback = NULL;

    unlock(p);
    lock_fini(p->lock);                      // <----- Δ with HAFNIUM
    free(p);                                 // <----- Δ with HAFNIUM
  }



  static void *alloc_no_fallback(struct mpool *p) { 
    void *ret;
    struct mpool_chunk *chunk;
    struct mpool_chunk *new_chunk;

    lock(p);
    if (p->entry_list != NULL) {
        struct mpool_entry *entry = p->entry_list;

        p->entry_list = entry->next;
        ret = entry;
        goto exit;
    }

    chunk = p->chunk_list;
    if (chunk == NULL) {
        ret = NULL;
        goto exit;
    }

    new_chunk = (struct mpool_chunk *)((uintptr_t)chunk + p->entry_size);
    if (new_chunk >= chunk->limit) {
        p->chunk_list = chunk->next_chunk;
    } else {
        *new_chunk = *chunk;
        p->chunk_list = new_chunk;
    }

    ret = chunk;

exit:
    unlock(p);

    return ret;
  }



  void *alloc(struct mpool *p) {
    do {
        void *ret = alloc_no_fallback(p);

        if (ret != NULL) {
            return ret;
        }

        p = p->fallback;
    } while (p != NULL);

    return NULL;
  }
 
 
 
  void free(struct mpool *p, void *ptr) {
    struct mpool_entry *e = ptr;

    lock(p);
    e->next = p->entry_list;
    p->entry_list = e;
    unlock(p);
  }



  static void lock(struct mpool *p)
  {
    if (mpool_locks_enabled) {
        sl_lock(&p->lock);
    }
  }



  static void unlock(struct mpool *p)
  {
    if (mpool_locks_enabled) {
        sl_unlock(&p->lock);
    }
  }
}
