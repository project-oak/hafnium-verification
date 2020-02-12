[** After Typechecking **]
[** There are NO Yield/Lock **]

(before) val := undef | nodef | int | .. | ptr(mem_addr: int)
(now)    val := undef | nodef | int | .. | ptr(mem_contents: list val)
(not sure)                               | readonly_ptr(mem_contents: list val)
//YJ: nodef can be encoded as: readonly_ptr([]).

Immutable borrow  : copy
Move              : make original value to "nodef" and then copy
Mutable borrow    : No such thing. Just use move 
//YJ: need to understand more. What is the differente btw. Rust? 
//We don't need care about compilation/speed?

//Q: Do we need "readonly" tag? 
//YJ: I don't think we need it.
//If we need it, I think we should attach it in value, not name.
//"name = MyStruct { a: T, b: T }" --> immutable borrow a, move b


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
  void mpool_init(struct mpool *p, size_t entry_size)
  {
    p->entry_size = entry_size;
    p->chunk_list = NULL;
    p->entry_list = NULL;
    p->fallback = NULL;
  }
 
  void fini(struct mpool *p) {
	struct mpool_entry *entry;
	struct mpool_chunk *chunk;

    if (!p->fallback) {
        return;
    }

    entry =[MOVE] p->entry_list;
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
  }



  static void *alloc_no_fallback(struct mpool *p) { 
    void *ret;
    struct mpool_chunk *chunk;
    struct mpool_chunk *new_chunk;

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

    e->next = p->entry_list;
    p->entry_list = e;
  }

}
