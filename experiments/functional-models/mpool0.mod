[** Original Hafnium **]
[** Every line has Yield but omitted **]

struct mpool_chunk {
	struct mpool_chunk *next_chunk;
	struct mpool_chunk *limit;
};

struct mpool_entry {
	struct mpool_entry *next;
};

struct mpool {
  struct spinlock lock;
  size_t entry_size;
  struct mpool_chunk *chunk_list;
  struct mpool_entry *entry_list;
  struct mpool *fallback;
};

Module MPOOL {
  void mpool_init(struct mpool *p, size_t entry_size)
  {
    p->entry_size = entry_size;
    p->chunk_list = NULL;
    p->entry_list = NULL;
    p->fallback = NULL;
    sl_init(&p->lock);
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

  void *mpool_alloc_contiguous_no_fallback(struct mpool *p, size_t count,
					 size_t align)
  {
    struct mpool_chunk **prev;
    void *ret = NULL;
  
    align *= p->entry_size;
  
    mpool_lock(p);
  
    prev = &p->chunk_list;
    while ( *prev != NULL) {
      uintptr_t start;
      struct mpool_chunk *new_chunk;
      struct mpool_chunk *chunk = *prev;
  
      start = (((uintptr_t)chunk + align - 1) / align) * align;
  
      new_chunk =
        (struct mpool_chunk *)(start + (count * p->entry_size));
      if (new_chunk <= chunk->limit) {
        if (new_chunk == chunk->limit) {
          *prev = chunk->next_chunk;
        } else {
          *new_chunk = *chunk;
          *prev = new_chunk;
        }
  
        if (start - (uintptr_t)chunk >= p->entry_size) {
          chunk->next_chunk = *prev;
          *prev = chunk;
          chunk->limit = (struct mpool_chunk *)start;
        }
  
        ret = (void *)start;
        break;
      }
  
      prev = &chunk->next_chunk;
    }
  
    mpool_unlock(p);
  
    return ret;
  }

  void *mpool_alloc_contiguous(struct mpool *p, size_t count, size_t align)
  {
    do {
      void *ret = mpool_alloc_contiguous_no_fallback(p, count, align);
  
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
