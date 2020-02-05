[** YIELD NOT OMITTED **]

// Concurrency Abstraction

Id: Type := Int64;
Page: Type := Int64;
Mpool: Type := { 
  is_running: Bool;
  lock: SPINLOCK.Id, entry_size: size_t, chunk_list: List<Page>,
  entry_list: List<(Page, Page)>, fallback: Id?
}

Module MPOOL2 {
  manager: Id -> Mpool? := (fun _ => None);
  lock_enabled: Bool := false;
  
  fun new(entry_size: size_t): Id {
    // Δ: Removed most of the YIELDs
    new_id := manager.fresh_id();
    lock := [** SPINLOCK.new() **];
    manager[new_id] := Some(Mpool { false, lock, entry_size, nil, nil, None });
    return new_id
  }
 
  fun fini(p: Id): Unit {
    // Δ: Removed most of the YIELDs
    mpool := manager[p].get!();
    [** YIELD **]
	if (mpool.fallback == None) { return; }
    [** YIELD **]
    lock(p);
    assume!(mpool.is_running = false);            // <----- Δ
    mpool.is_running = true;                      // <----- Δ

    List<Page> entry;
    List<(Page, Page)> chunk;

    manager[p] := None;
    
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

    mpool.is_running = false;                     // <----- Δ
    unlock(p);
  }
  
  fun alloc_no_fallback(p: Id): Page {
    // Δ: Removed most of the YIELDs
    mpool := manager[p].get!();
    [** YIELD **]

    lock(p);
    Page ret;
    assume!(mpool.is_running = false);            // <----- Δ
    mpool.is_running = true;                      // <----- Δ
    if let (hd :: tl) := mpool.entry_list {
        ret := hd;

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
        mpool.chunk_list := (new_chunk, to) :: tl
    }

    ret := from;

exit:
    mpool.is_running = false;                     // <----- Δ
    unlock(p);
    [** YIELD **]
    return ret;
  }
  
  fun alloc(p: Id): Page {
    loop {
        [** YIELD **]
        Page ret := alloc_no_fallback(p);
        [** YIELD **]

        if (ret != NULL) {
            [** YIELD **]
            return ret;
        }

        [** YIELD **]
        match manager[p].get!().fallback with
        | Some id => [** YIELD **] p := id
        | None => [** YIELD **] break
        end
    }
    [** YIELD **]
    return NULL;
  }

  fun free(p: Id, ptr: Page): Unit {
    lock(p);
    assume!(mpool.is_running = false);            // <----- Δ
    mpool.is_running = true;                      // <----- Δ
    mpool := manager[p].get!();
    mpool.entry_list := ptr :: mpool.entry_list;
    mpool.is_running = false;                     // <----- Δ
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
