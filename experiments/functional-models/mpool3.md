//Concurrency Abstraction
//SimRel:

Id: Type := Int64;
Mpool: Type := { 
  isRunning: bool; //This is new
  <<MPOOL1.Mpool>>
}

//YJ: I think we need liveness of CPU scheduler, to remove some [** YIELD **]s

Module MPOOL2 {
  manager: Id -> Mpool? := (fun _ => None);

  fun new(entry_size: size_t): Id {
    newId := manager.fresh_Id();
    malloc_with_undef(sizeof(mpool));
    lock := [** sl_new() **];
    manager[newId] := Some(Mpool { false, lock, entry_size, NULL, NULL, NULL });
    return newId
  }
 
 fun fini(p: Id): unit {
    mpool := manager[p].get!();
    [** sl_lock(mpool.lock) **];
    Atomic {
      manager[p] := None;
      <<Mpool0.fini - lock - unlock>>;
    }
    [** sl_unlock(mpool.lock) **]
  }
  
  fun mpool_alloc_no_fallback(p: Id): Page {
    mpool = manager[p].get!();
    <<Mpool0.mpool_alloc_no_fallback>>
  }
  
  fun alloc(p: Id): Page {
    mpool = manager[p].get!();
    <<Mpool0.alloc>>
  }

  fun free(p: Id, ptr: Page): unit {
    mpool := manager[p].get!();
    <<Mpool0.free>>
  }
}
