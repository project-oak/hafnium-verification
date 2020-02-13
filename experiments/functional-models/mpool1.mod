[** After Typechecking **]
[** There are NO Yield/Lock **]

(before) val := undef | nodef | int | .. | ptr(mem_addr: int)
(now)    val := undef | nodef | int | .. | ptr(mem_contents: list val)
(not sure)                               | readonly_ptr(mem_contents: list val)
//YJ: maybe, nodef can be encoded as: readonly_ptr([]).

Immutable borrow  : make "ptr" to "readonly_ptr" and then copy
Move              : make original value to "nodef" and then copy
Mutable borrow    : In semantics, there is no such thing. It is just syntactic sugar.

bool func(int *[BORROW]x, int *[BORROW]y) {
  *x = 10;
  return true;
}
~~~>
(bool, int *x, int *y) func(int *[MOVE]x, int *[MOVE]y) {
  *x = 10;
  RETURN_PUSH([MOVE]y);
  RETURN_PUSH([MOVE]x);
  return true;
}


//Q: Do we need "readonly" tag?
//Pros: giving more NB (keeping more invariants from type checking)
//Cons: semantics will be more complex;
//      esp. because we need to model "readonly_ptr" -> "ptr".

//YJ: I doubt if we need it.
//If we need it, I suggest to attach it in value (like "readonly_ptr" above), not name.
//1) Splitting borrows: "name = MyStruct { a: T, b: T }" --> immutable borrow a, move b
//2) Want to allow this: { let mut a: &i32 = &5; a = &10; }

struct mpool_chunk {
	struct mpool_chunk *next_chunk;
	struct mpool_chunk *limit;
};

struct mpool_entry {
	struct mpool_entry *next;
};

struct mpool {
  size_t entry_size;
  struct mpool_chunk *chunk_list;
  struct mpool_entry *entry_list;
  struct mpool *fallback;
};

Module MPOOL {
  void mpool_init(struct mpool *[BORROW]p, size_t entry_size)
  {
    p->entry_size = entry_size;
    p->chunk_list = NULL;
    p->entry_list = NULL;
    p->fallback = NULL;
  }
 
  void fini(struct mpool *[MOVE]p) {
	struct mpool_entry *entry;
	struct mpool_chunk *chunk;

    if (!p->fallback) {
        return;
    }

    entry =[MOVE] p->entry_list;
    while (entry != NULL) {
        void *ptr = entry;

        entry =[MOVE] entry->next;
        free([BORROW]p->fallback, ptr);
    }

    chunk =[MOVE] p->chunk_list;
    while (chunk != NULL) {
        void *ptr = chunk;
        size_t size = (uintptr_t)chunk->limit - (uintptr_t)chunk;

        chunk = chunk->next_chunk;
        add_chunk([BORROW]p->fallback, ptr, size);
    }

    p->chunk_list = NULL;
    p->entry_list = NULL;
    p->fallback = NULL;
  }



  static void *alloc_no_fallback(struct mpool *[BORROW]p) { 
    void *ret;
    struct mpool_chunk *chunk;
    struct mpool_chunk *new_chunk;

    if (p->entry_list != NULL) {
        struct mpool_entry *entry =[MOVE] p->entry_list;

        p->entry_list =[MOVE] entry->next;
        ret =[MOVE] entry;
        goto exit;
    }

    chunk =[MOVE] p->chunk_list;
    if (chunk == NULL) {
        ret = NULL;
        goto exit;
    }

    //YJ: @minki suggested to abstract "ptr" to "struct" in this level, but I am against it.
    //This code essentially assumes memory structure.

    new_chunk =[MOVE] (struct mpool_chunk *)((uintptr_t)chunk + p->entry_size);
    //IMPORTANT: We are doing "PTR->INT" cast, and then integer comparison.
    //Sol 1 --> use (offset: int) instead of (limit: ptr). (is it general?)
    //Sol 2 --> mem_contents should have address...
    // which is basically equal to: maintain global memory (to guarantee freshness of addr),
    // and ptr(from to: int) asserts ownership... This requires each value to have unique id

    if (new_chunk >= chunk->limit) {
        p->chunk_list =[MOVE] chunk->next_chunk;
    } else {
        *new_chunk = *chunk;
        p->chunk_list =[MOVE] new_chunk;
    }

    ret =[MOVE] chunk;

exit:
    return ret;
  }



  void *alloc(struct mpool *[BORROW]p) {
    do {
        void *ret = alloc_no_fallback([BORROW]p);

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
  
    /*
     * Go through the chunk list in search of one with enough room for the
     * requested allocation
     */
    prev = &p->chunk_list;
    while (*prev != NULL) {
      uintptr_t start;
      struct mpool_chunk *new_chunk;
      struct mpool_chunk *chunk = *prev;
  
      /* Round start address up to the required alignment. */
      start = (((uintptr_t)chunk + align - 1) / align) * align;
  
      /*
       * Calculate where the new chunk would be if we consume the
       * requested number of entries. Then check if this chunk is big
       * enough to satisfy the request.
       */
      new_chunk =
        (struct mpool_chunk *)(start + (count * p->entry_size));
      if (new_chunk <= chunk->limit) {
        /* Remove the consumed area. */
        if (new_chunk == chunk->limit) {
          *prev = chunk->next_chunk;
        } else {
          *new_chunk = *chunk;
          *prev = new_chunk;
        }
  
        /*
         * Add back the space consumed by the alignment
         * requirement, if it's big enough to fit an entry.
         */
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

    e->next = p->entry_list;
    p->entry_list = e;
  }

}
