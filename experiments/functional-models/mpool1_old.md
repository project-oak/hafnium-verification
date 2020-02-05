//YJ: 중간단계를 더 두는건 비효율적인 듯
//C도 아니고 spec language도 아닌 이상한 언어로 쓴 이상한 상태를 만들어서
//IGNORE BELOW



[** EVERY LINE HAS YIELD BUT OMITTED **]

//Memory Abstraction
//SimRel: ([*SRC*] manager[id] = Some(Mpool { data }) <->
           [*TGT*] Mem[id] contains "struct mpool" with "data")
       /\ ([*SRC*] Mem[x] == [*TGT*] Mem[x] \/ [*SRC*] Mem[x] = Undef Value)

Id: Type := Int64;
Mpool: Type := { 
  lock: spinlock*, entry_size: size_t, chunk_list: mpool_chunk*, 
  entry_list: mpool_entry*, fallback: mpool*
}

Module MPOOL1 {
  manager: Id -> Mpool? := (fun _ => None);

  fun new(entry_size: size_t): Id {
    newId := manager.freshId();
    malloc_with_undef(sizeof(mpool));
    lock := [** sl_new() **];
    [** YIELD **] * 5;
    manager[newId] := Some(Mpool { false, lock, entry_size, NULL, NULL, NULL });
    [** YIELD **];
    return newId
  }
 
 fun fini(p: Id): unit {
    mpool := manager[p].get!();
    [** sl_lock(mpool.lock) **];
    manager[p] := None;
    <<Mpool0.fini - lock - unlock>>;
    [** sl_unlock(mpool.lock) **]
  }
  
  fun alloc_no_fallback(p: Id): Page {
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

//YJ: instruction 추가로 interleaving 더 생기게 해도 되고 (SRC 행동이 더 많음) 
//저기는 YIELD 빼도 되고. 이게 더 쉬울 듯

//YJ: SRC Mem[id] 부분이 우연히 다른 곳에서 allocate 되면 안된다는거 어떻게 확보?
//memory model에서, malloc이 여기는 할당 못하도록 모종의 표시?
//Logical Memory?
