[** After Typechecking **]
[** There are NO Yield/Lock **]

(before) val := undef | nodef | int | .. | ptr(mem_addr: int)
(now)    val := undef | nodef | int | .. | ptr(mem_contents: list val)
(not sure)                               | readonly_ptr(mem_contents: list val)
//YJ: maybe, nodef can be encoded as: readonly_ptr([]).

Immutable borrow  : make "ptr" to "readonly_ptr" and then copy
Move              : make original value to "nodef" and then copy
Mutable borrow    : No such thing. Just use move 
//YJ: need to understand more. What is the differente btw. Rust? 
//We don't need care about compilation/speed?

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
  void mpool_init(struct mpool *[MOVE]p, size_t entry_size)
  {
    p->entry_size = entry_size;
    p->chunk_list = NULL;
    p->entry_list = NULL;
    p->fallback = NULL;
    //[RETURN]p
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
    //[RETURN]p
  }



  static void *alloc_no_fallback(struct mpool *[MOVE]p) { 
    void *ret;
    struct mpool_chunk *chunk;
    struct mpool_chunk *new_chunk;

    if (p->entry_list != NULL) {
        struct mpool_entry *entry =[MOVE] p->entry_list;

        p->entry_list = entry->next;
        ret = entry;
        goto exit;
    }

    chunk[MOVE] = p->chunk_list;
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
    //[RETURN]p
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
