[** EVERY LINE HAS YIELD BUT OMITTED **]
[** Some "nop"s are inserted to match with YIELD from mpool0 **]

// Memory & Data Abstraction
// SimRel: ([*SRC*] manager[id] = Some(Mpool { data }) <->
            [*TGT*] Mem[id] contains "struct mpool" with "data")
        /\ (for other parts of the memory, source and target are the same)

?: option type
!: UB
¡: NB
MODULENAME
TypeName
variable_name
variableName

Id: Type := Int64;
Page: Type := Int64;
Mpool: Type := { 
  lock: SPINLOCK.Id, entry_size: size_t, chunk_list: List<Page>,
  entry_list: List<(Page, Page)>, fallback: Id?
}

Module MPOOL1 {
  manager: Id -> Mpool? := (fun _ => None);
  lock_enabled: Bool := false;
  
  fun new(entry_size: size_t): Id {
    new_id := manager.fresh_id();
    nop;
    nop;
    nop;
    lock := [** SPINLOCK.new() **];
    manager[new_id] := Some(Mpool { false, lock, entry_size, nil, nil, None }); // <--- Δ
    return new_id
  }
  //YJ: C에서 malloc하는 부분이랑 맞춰서 malloc_with_undef 같은걸 부를 수도 있는데,
  //장점: CompCert의 memory extension 같은게 성립하고, 임의의 코드가 self-related 됨
  //단점: memory-irrelevant 같은 이야기 하기가 힘듦
 
  fun fini(p: Id): Unit {
    List<Page> entry;
    List<(Page, Page)> chunk;

    mpool := manager[p].get!();
	if (mpool.fallback == None) { return; }
    lock(p);

    manager[p] := None;                           // <----- Δ
    
    entry := mpool.entry_list;
    while (entry != nil) {
        Page ptr := entry.head¡();
        entry := entry.tail¡();
        mpool_free(mpool.fallback, ptr);
    }

    chunk = mpool.chunk_list;
    while (chunk != nil) {
        Page ptr := chunk.head¡().(fst);
        size_t size := chunk.head¡().(snd) - chunk.head¡().(fst);

        chunk := chunk.tail¡();
        mpool_add_chunk(mpool.fallback, ptr, size);
    }

    mpool.chunk_list := nil;
    mpool.entry_list := nil;
    mpool.fallback := None;

    unlock(p);
    SPINLOCK.fini(mpool.lock);                   // <----- Δ with HAFNIUM
    nop
  }
  
  fun alloc_no_fallback(p: Id): Page {
    mpool := manager[p].get!();
    Page ret;

    lock(p);
    if let (hd :: tl) := mpool.entry_list {
        ret := hd;

        nop;
        mpool.entry_list := tl;
        goto exit;
    }

    chunk = mpool.chunk_list;
    if (chunk == nil) {
        ret := NULL;
        goto exit;
    }

    let¡ ((from, to) :: tl) = chunk;
    new_chunk := from + mpool.entry_size;
    if (new_chunk >= to) {
        mpool.chunk_list := tl;
        p->chunk_list := chunk->next_chunk;
    } else {
        nop;
        mpool.chunk_list := (new_chunk, to) :: tl
    }

    ret := from;

exit:
    unlock(p);
    return ret;
  }
  
  fun alloc(p: Id): Page {
    loop {
        Page ret := alloc_no_fallback(p);

        if (ret != NULL) {
            return ret;
        }

        match manager[p].get!().fallback with
        | Some id => p := id
        | None => break
        end
    }

    return NULL;
  }

  fun free(p: Id, ptr: Page): Unit {
    nop;
    lock(p);
    mpool := manager[p].get!();
    mpool.entry_list := ptr :: mpool.entry_list;
    unlock(p);
  }

  fun lock(mpool: Mpool): Unit {
    if (lock_enabled) {
      mpool := manager[p].get!();
      [** SpinLock.lock(mpool->lock); **]
    }
  }

  fun unlock(mpool: Mpool): Unit {
    if (lock_enabled) {
      mpool := manager[p].get!();
      [** SpinLock.unlock(mpool->lock); **]
    }
  }
}
