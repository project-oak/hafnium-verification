(*
 * Copyright 2020 Youngju Song
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     RelDec
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

From ITree Require Import
     ITree ITreeFacts.

Import ITreeNotations.
Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.
Require Import Coqlib sflib.


(* From HafniumCore *)
Require Import Lang Lock.
Import LangNotations.


Require Import Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.
Require Import BitNat.

Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Local Open Scope N_scope.



Set Implicit Arguments.



Definition DebugMpool := Syscall "md".


Module MPOOLCONCUR.

  (*
Simplified Mpool := Vptr [Vnat//lock ; Vptr//chunk_list ; Vptr//fallback]
   *)

  Definition lock_ofs := 0.
  Definition chunk_list_ofs := 1.
  Definition fallback_ofs := 2.
  Definition next_chunk_ofs := 0.
  Definition limit_ofs := 1.

  Definition entry_size: N := 4.

  Fixpoint chunk_list_wf (chunk_list: val): bool :=
    match chunk_list with
    | Vptr paddr cts =>
      is_some paddr &&
      match cts with
      | [] => true
      | _ :: []  => false
      | next_chunk :: limit :: _ =>
        match limit with
        | Vnat limit =>
          if ((N.of_nat (length cts)) =? (limit * entry_size))
          then chunk_list_wf next_chunk 
          else false
        | _ => false
        end
      end
    | _ => false
    end
  .

  Definition lock_wf (lock: val): bool :=
    match lock with
    | Vnat _ => true
    | _ => false
    end
  .

  Fixpoint mpool_wf (p: val): bool :=
    match p with
    | Vptr _ p =>
      match p with
      | [] => true
      | [ lock ; chunk_list ; fallback ] =>
        chunk_list_wf chunk_list && mpool_wf fallback && lock_wf lock
      | _ => false
      end
    | _ => false
    end
  .







  (* void init(struct mpool *p, size_t entry_size) *)
  (* { *)
  (*   p->entry_size = entry_size; *)
  (*   p->chunk_list = NULL; *)
  (*   p->entry_list = NULL; *)
  (*   p->fallback = NULL; *)
  (*   sl_init(&p->lock); *)
  (* } *)

  (*** DELTA: Use function return value instead of borrowing && Add call to "Lock.release" **)
  Definition mpool_init (p: var): stmt :=
    (p @ chunk_list_ofs #:= Vnull) #;
    (p @ fallback_ofs   #:= Vnull) #;
    (p @ lock_ofs       #:= (Call "Lock.new" [])) #;
    (Call "Lock.release" [CBV (p #@ lock_ofs) ; CBV p]) #;
    Skip
  .

  (* void mpool_init_with_fallback(struct mpool *p, struct mpool *fallback) *)
  (* { *)
  (* 	mpool_init(p, fallback->entry_size); *)
  (* 	p->fallback = fallback; *)
  (* } *)

  (*** DELTA: Add call to "Lock.release"  ***)
  Definition init_with_fallback (p fallback: var): stmt :=
    (* Call "init" [CBR p] #; *)
    (* (Store p fallback_ofs fallback) #; *)
    (* (Call "Lock.release" [CBV (p #@ lock_ofs) ; CBV p]) #; *)
    (p @ chunk_list_ofs #:= Vnull) #;
    (p @ fallback_ofs   #:= fallback) #;
    (p @ lock_ofs       #:= (Call "Lock.new" [])) #;
    (Call "Lock.release" [CBV (p #@ lock_ofs) ; CBV p]) #;
    Skip
  .

  (* void mpool_fini(struct mpool *p) *)
  (* { *)
  (* 	struct mpool_entry *entry; *)
  (* 	struct mpool_chunk *chunk; *)

  (* 	if (!p->fallback) { *)
  (* 		return; *)
  (* 	} *)

  (* 	mpool_lock(p); *)

  (* 	/* Merge the freelist into the fallback. */ *)
  (* 	entry = p->entry_list; *)
  (* 	while (entry != NULL) { *)
  (* 		void *ptr = entry; *)

  (* 		entry = entry->next; *)
  (* 		mpool_free(p->fallback, ptr); *)
  (* 	} *)

  (* 	/* Merge the chunk list into the fallback. */ *)
  (* 	chunk = p->chunk_list; *)
  (* 	while (chunk != NULL) { *)
  (* 		void *ptr = chunk; *)
  (* 		size_t size = (uintptr_t)chunk->limit - (uintptr_t)chunk; *)

  (* 		chunk = chunk->next_chunk; *)
  (* 		mpool_add_chunk(p->fallback, ptr, size); *)
  (* 	} *)

  (* 	p->chunk_list = NULL; *)
  (* 	p->entry_list = NULL; *)
  (* 	p->fallback = NULL; *)

  (* 	mpool_unlock(p); *)
  (* } *)
  (*** Reversed instruction order ***)
  Definition fini (p: var)
             (chunk size: var): stmt :=
    #if !(p #@ fallback_ofs)
     then Return Vnull
     else Skip #;
    p #= (Call "Lock.acquire" [CBV (p #@ lock_ofs)]) #;
    chunk #= (p #@ chunk_list_ofs) #;
    #while (chunk)
    do (
      size #= (chunk #@ limit_ofs) #;
      (*** Below two instructions' order is reversed from original code ***)
      Call "add_chunk" [CBV (p #@ fallback_ofs) ; CBV chunk ; CBV size] #;
      chunk #= (chunk #@ next_chunk_ofs)
    ) #;
    p @ chunk_list_ofs #:= Vnull #;
    p @ fallback_ofs   #:= Vnull #;
    (Call "Lock.release" [CBV (p #@ lock_ofs) ; CBV p]) #;
    Skip
  .
  
  (*
   void *mpool_alloc(struct mpool *p)
   {   
       do {
               void *ret = mpool_alloc_no_fallback(p);
       
               if (ret != NULL) {
                       return ret;
               }
       
               p = p->fallback;
       } while (p != NULL);
       
       return NULL;
   }   
   *)
  Definition alloc
             (p count: var)
             (ret next nextp: var): stmt :=
    #guarantee (CoqCode [CBV p] (fun p => (mpool_wf (nth 0 p Vnull): val, nil))) #;
    Debug "[alloc] locking" Vnull #;
    p #= (Call "Lock.acquire" [CBV (p #@ lock_ofs)]) #;
    next #= (p #@ chunk_list_ofs) #;
    Debug "[alloc] calling alloc_no_fallback" Vnull #;
    ret #= (Call "alloc_no_fallback" [CBR next]) #;
    p @ chunk_list_ofs #:= next #;
    Debug "[alloc] unlocking" Vnull #;
    (Call "Lock.release" [CBV (p #@ lock_ofs) ; CBV p]) #;
    #if (ret)
     then (DebugMpool "After alloc: " p #;
                      DebugShow "alloced: " ret #;
                      Return ret)
     else (
         nextp #= (p #@ fallback_ofs) #;
         #if (! nextp) then Return Vnull else Skip #;
         Debug "[alloc] calling alloc" Vnull #;
         ret #= (Call "alloc" [CBR nextp ; CBV count]) #;
         (p @ fallback_ofs #:= nextp) #;
         DebugMpool "After alloc: " p #;
         DebugShow "alloced: " ret #;
         Return ret
       )
  .
  

  (* JIEUNG: I need to add missing statements in  mpool_alloc_contiguous *)  
  (* void *mpool_alloc_contiguous(struct mpool *p, size_t count, size_t align) *)
  (* { *)
  (*   do { *)
  (*     void *ret = mpool_alloc_contiguous_no_fallback(p, count, align); *)
  
  (*     if (ret != NULL) { *)
  (*       return ret; *)
  (*     } *)
  
  (*     p = p->fallback; *)
  (*   } while (p != NULL); *)
  
  (*   return NULL; *)
  (* } *)

  (*** DELTA: while -> recursion && call no_fallback with chunk_list, not mpool ***)
  (*** DELTA: We lock here, not in "alloc_contiguous_no_fallback" ***)
  Definition alloc_contiguous
             (p count: var)
             (ret next nextp: var): stmt :=
    #guarantee (CoqCode [CBV p] (fun p => (mpool_wf (nth 0 p Vnull): val, nil))) #;
    Debug "[alloc_contiguous] locking" Vnull #;
    p #= (Call "Lock.acquire" [CBV (p #@ lock_ofs)]) #;
    next #= (p #@ chunk_list_ofs) #;
    Debug "[alloc_contiguous] calling alloc_contiguous_no_fallback" Vnull #;
    ret #= (Call "alloc_contiguous_no_fallback" [CBR next ; CBV count]) #;
    p @ chunk_list_ofs #:= next #;
    Debug "[alloc_contiguous] unlocking" Vnull #;
    (Call "Lock.release" [CBV (p #@ lock_ofs) ; CBV p]) #;
    #if (ret)
     then (DebugMpool "After alloc_contiguous: " p #;
                      DebugShow "alloced: " ret #;
                      Return ret)
     else (
         nextp #= (p #@ fallback_ofs) #;
         #if (! nextp) then Return Vnull else Skip #;
         Debug "[alloc_contiguous] calling alloc_contiguous" Vnull #;
         ret #= (Call "alloc_contiguous" [CBR nextp ; CBV count]) #;
         (p @ fallback_ofs #:= nextp) #;
         DebugMpool "After alloc_contiguous: " p #;
         DebugShow "alloced: " ret #;
         Return ret
       )
  .

   (*
    static void *mpool_alloc_no_fallback(struct mpool *p)
    {  
          void *ret;
          struct mpool_chunk *chunk;
          struct mpool_chunk *new_chunk;
   
          /* Fetch an entry from the free list if one is available. */
          mpool_lock(p);
          if (p->entry_list != NULL) {
                  struct mpool_entry *entry = p->entry_list;
   
                  p->entry_list = entry->next;
                  ret = entry;
                  goto exit;
          }
   
          /* There was no free list available. Try a chunk instead. */
          chunk = p->chunk_list;
          if (chunk == NULL) {
                  /* The chunk list is also empty, we're out of entries. */
                  ret = NULL;
                  goto exit;
          }
   
          new_chunk = (struct mpool_chunk * )((uintptr_t)chunk + p->entry_size);
          if (new_chunk >= chunk->limit) {
                  p->chunk_list = chunk->next_chunk;
          } else {
                  *new_chunk = *chunk;
                  p->chunk_list = new_chunk;
          }
   
          ret = chunk;
   
    exit:
          mpool_unlock(p);
   
          return ret;
    }  
   *)
  

  (*** DELTA: while -> recursion && "limit" ptr -> offset "nat" && no alignment ***)
  Definition alloc_no_fallback
             (cur: var)
             (ret next cur_ofs new_cur: var): stmt :=
    #if ! cur then Return Vnull else Skip #;
    cur_ofs #= (cur #@ limit_ofs) #;
    new_cur #= (SubPointerFrom cur  entry_size) #;
    new_cur @ next_chunk_ofs #:= (cur #@ next_chunk_ofs) #;
    new_cur @ limit_ofs #:= (cur_ofs - 1) #;
    ret #= (SubPointerTo cur entry_size) #;
    cur #= new_cur #;
    Return ret.

  (* void *mpool_alloc_contiguous_no_fallback(struct mpool *p, size_t count, *)
  (*       				 size_t align) *)
  (* { *)
  (*   struct mpool_chunk **prev; *)
  (*   void *ret = NULL; *)
  
  (*   align *= p->entry_size; *)
  
  (*   mpool_lock(p); *)
  
  (*   prev = &p->chunk_list; *)
  (*   while ( *prev != NULL) { *)
  (*     uintptr_t start; *)
  (*     struct mpool_chunk *new_chunk; *)
  (*     struct mpool_chunk *chunk = *prev; *)
  
  (*     start = (((uintptr_t)chunk + align - 1) / align) * align; *)
  
  (*     new_chunk = *)
  (*       (struct mpool_chunk * )(start + (count * p->entry_size)); *)
  (*     if (new_chunk <= chunk->limit) { *)
  (*       if (new_chunk == chunk->limit) { *)
  (*         *prev = chunk->next_chunk; *)
  (*       } else { *)
  (*         *new_chunk = *chunk; *)
  (*         *prev = new_chunk; *)
  (*       } *)
  
  (*       if (start - (uintptr_t)chunk >= p->entry_size) { *)
  (*         chunk->next_chunk = *prev; *)
  (*         *prev = chunk; *)
  (*         chunk->limit = (struct mpool_chunk * )start; *)
  (*       } *)
  
  (*       ret = (void * )start; *)
  (*       break; *)
  (*     } *)
  
  (*     prev = &chunk->next_chunk; *)
  (*   } *)
  
  (*   mpool_unlock(p); *)
  
  (*   return ret; *)
  (* } *)

  (*** DELTA: while -> recursion && "limit" ptr -> offset "nat" && no alignment ***)
  Definition alloc_contiguous_no_fallback
             (cur count: var)
             (ret next cur_ofs new_cur: var): stmt :=
    #if ! cur then Return Vnull else Skip #;
    cur_ofs #= (cur #@ limit_ofs) #;
    #if (count <= cur_ofs)
     then (
           (Debug "If1-limit: " cur_ofs) #;
           #if count == cur_ofs
            then (
                ret #= (SubPointerTo cur (count * entry_size)) #;
                cur #= (cur #@ next_chunk_ofs) #;
                Return ret
              )
            else (
                new_cur #= (SubPointerFrom cur (count * entry_size)) #;
                new_cur @ next_chunk_ofs #:= (cur #@ next_chunk_ofs) #;
                new_cur @ limit_ofs #:= (cur_ofs - count) #;
                ret #= (SubPointerTo cur (count * entry_size)) #;
                cur #= new_cur #;
                Return ret
              )
          )
     else (
         (Debug "Else1-limit: " cur_ofs) #;
         next #= (cur #@ next_chunk_ofs) #;
         ret #= (Call "alloc_contiguous_no_fallback" [CBR next ; CBV count]) #;
         cur @ next_chunk_ofs #:= next #;
         Return ret
         )
  .

  (* bool mpool_add_chunk(struct mpool *p, void *begin, size_t size) *)
  (* { *)
  (* 	struct mpool_chunk *chunk; *)
  (* 	uintptr_t new_begin; *)
  (* 	uintptr_t new_end; *)

  (* 	/* Round begin address up, and end address down. */ *)
  (* 	new_begin = ((uintptr_t)begin + p->entry_size - 1) / p->entry_size * *)
  (* 		    p->entry_size; *)
  (* 	new_end = ((uintptr_t)begin + size) / p->entry_size * p->entry_size; *)

  (* 	/* Nothing to do if there isn't enough room for an entry. */ *)
  (* 	if (new_begin >= new_end || new_end - new_begin < p->entry_size) { *)
  (* 		return false; *)
  (* 	} *)

  (* 	chunk = (struct mpool_chunk * )new_begin; *)
  (* 	chunk->limit = (struct mpool_chunk * )new_end; *)

  (* 	mpool_lock(p); *)
  (* 	chunk->next_chunk = p->chunk_list; *)
  (* 	p->chunk_list = chunk; *)
  (* 	mpool_unlock(p); *)

  (* 	return true; *)
  (* } *)

  (*** DELTA: no alignment ***)
  Definition add_chunk
             (p begin size: var)
             (chunk: var): stmt :=
    chunk #= begin #;
    (* Store chunk limit_ofs ((GetLen chunk) / entry_size) #; *)
    chunk @ limit_ofs #:= size #;

    Debug "add_chunk-calling lock" p #;
    p #= (Call "Lock.acquire" [CBV (p #@ lock_ofs)]) #;
    chunk @ next_chunk_ofs #:= (p #@ chunk_list_ofs) #;
    p @ chunk_list_ofs #:= chunk #;
    DebugMpool "After add_chunk: " p #;
    (Call "Lock.release" [CBV (p #@ lock_ofs) ; CBV p]) #;
    Skip
  .
  Definition mpool_initF: function. mk_function_tac mpool_init ["p"] ([]: list var). Defined.
  Definition init_with_fallbackF: function.
    mk_function_tac init_with_fallback ["p" ; "fb"] ([]: list var). Defined.
  Definition finiF: function.
    mk_function_tac fini ["p" ] ["chunk" ; "size"]. Defined.

  Definition allocF: function.
    mk_function_tac alloc ["p" ; "count"] ["ret" ; "next" ; "nextp"]. Defined.
  Definition alloc_no_fallbackF: function.
    mk_function_tac alloc_no_fallback
                    ["cur" ] ["ret" ; "next" ; "cur_ofs" ; "new_cur"]. Defined.

  Definition alloc_contiguousF: function.
    mk_function_tac alloc_contiguous ["p" ; "count"] ["ret" ; "next" ; "nextp"]. Defined.
  Definition alloc_contiguous_no_fallbackF: function.
    mk_function_tac alloc_contiguous_no_fallback
                    ["cur" ; "count"] ["ret" ; "next" ; "cur_ofs" ; "new_cur"]. Defined.
  Definition add_chunkF: function.
    mk_function_tac add_chunk ["p" ; "begin" ; "size"] ["chunk"]. Defined.

    Definition mpool_program: program :=
      [
        ("MPOOLCONCUR.mpool_init", mpool_initF) ;
      ("MPOOLCONCUR.init_with_fallback", init_with_fallbackF);
      ("MPOOLCONCUR.fini", finiF) ;
      ("alloc", allocF);
      ("alloc_no_fallback", alloc_no_fallbackF);
      ("alloc_contiguous", alloc_contiguousF);
      ("alloc_contiguous_no_fallback", alloc_contiguous_no_fallbackF);
      ("MPOOLCONCUR.add_chunk", add_chunkF)
      ].

    Definition mpool_modsem : ModSem := program_to_ModSem mpool_program.
    
(*
  Definition mpool_modsem: ModSem := program_to_ModSem program
  mk_ModSem
  (fun s => existsb (string_dec s) ["MPOOLCONCUR.mpool_init" ; "MPOOLCONCUR.init_with_fallback" ;
  "MPOOLCONCUR.fini" ; "MPOOLCONCUR.alloc_contiguous" ;
  "MPOOLCONCUR.alloc_contiguous_no_fallback" ;
  "MPOOLCONCUR.add_chunk"])
  (0, Maps.empty)
  LockEvent
  handler
  sem.
 *)
    
End MPOOLCONCUR.

Module TEST.

  Include MPOOLCONCUR.

  Definition big_chunk (paddr: N) (size: nat): val :=
    Vptr (Some paddr) (repeat (Vnat 0) ((N.to_nat entry_size) * size)).

  Module TEST1.

    Definition main
               (p r1 r2 r3: var): stmt :=
      p #= Vptr None [0: val ; 0: val ; 0: val] #;
        (* (Put "before init: " p) #; *)
        Debug "before init: " p #;
        Call "mpool_init" [CBR p] #;
        Debug "after init: " p #;
        Call "add_chunk" [CBR p ; CBV (big_chunk 500 10) ; CBV 10] #;
        (* (Put "add_chunk done: " p) #; *)
        Debug "add_chunk done: " p #;

        r1 #= Call "alloc_contiguous" [CBR p ; CBV 7] #;
        (* (Put "alloc first; should succeed: " r1) #; *)
        (* (Put "alloc first; p: " p) #; *)
        Debug "alloc_contiguous done: " p #;
        #assume r1 #;

        r2 #= Call "alloc_contiguous" [CBR p ; CBV 7] #;
        (* (Put "alloc second; should fail: " r2) #; *)
        (* (Put "alloc second; p: " p) #; *)
        Debug "alloc_contiguous done: " p #;
        #assume (!r2) #;

        Call "add_chunk" [CBR p ; CBV r1 ; CBV 7] #;
        (* (Put "add_chunk done" p) #; *)

        r3 #= Call "alloc_contiguous" [CBR p ; CBV 7] #;
        (* (Put "alloc third; should succeed: " r3) #; *)
        (* (Put "alloc third; p: " p) #; *)
        #assume r3 #;


        Put "Test1 Passed" Vnull #;
        Skip
    .
    Definition mainF: function.
      mk_function_tac main ([]: list var) ["p" ; "r1" ; "r2" ; "r3"]. Defined.

    Definition program: program :=
      [
        ("main", mainF) ;
          ("mpool_init", mpool_initF) ;
          ("alloc_contiguous", alloc_contiguousF) ;
          ("alloc_contiguous_no_fallback", alloc_contiguous_no_fallbackF) ;
          ("add_chunk", add_chunkF)
      ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem program ; LOCK.modsem]
      (* eval_multimodule [LOCK.modsem ; program_to_ModSem program] *)
    .

  End TEST1.

  Module TEST2.

    Definition main
               (p r1 r2 r3: var): stmt :=
      p #= Vptr None [0: val ; 0: val ; 0: val ] #;
        (* (Put "before init: " p) #; *)
        Call "mpool_init" [CBR p] #;
        (* (Put "after init: " p) #; *)
        Call "add_chunk" [CBR p ; CBV (big_chunk 500 10) ; CBV 10] #;
        Call "add_chunk" [CBR p ; CBV (big_chunk 1500 10) ; CBV 10] #;
        (* (Put "add_chunk done: " p) #; *)

        r1 #= Call "alloc_contiguous" [CBR p ; CBV 7] #;
        (* (Put "alloc first; should succeed: " r1) #; *)
        (* (Put "alloc first; p: " p) #; *)
        #assume r1 #;

        r2 #= Call "alloc_contiguous" [CBR p ; CBV 7] #;
        (* (Put "alloc second; should succeed: " r2) #; *)
        (* (Put "alloc second; p: " p) #; *)
        #assume r2 #;

        Put "Test2 Passed" Vnull #;
        Skip
    .
    Definition mainF: function.
      mk_function_tac main ([]: list var) ["p" ; "r1" ; "r2" ; "r3"]. Defined.

    Definition program: program :=
      [
        ("main", mainF) ;
          ("mpool_init", mpool_initF) ;
          ("alloc_contiguous", alloc_contiguousF) ;
          ("alloc_contiguous_no_fallback", alloc_contiguous_no_fallbackF) ;
          ("add_chunk", add_chunkF)
      ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem program ; LOCK.modsem].

  End TEST2.

  Module TEST3.

    (*** two tests with different add_chunk order ***)

    Definition main1
               (p0 p1 p2 r: var): stmt :=
      p0 #= Vptr None [0: val ; 0: val ; 0: val ] #;
      p1 #= Vptr None [0: val ; 0: val ; 0: val ] #;
      p2 #= Vptr None [0: val ; 0: val ; 0: val ] #;
      (* Call "mpool_init" [CBR p2] #; *)
      (* Call "add_chunk" [CBR p2 ; CBV (big_chunk 2500 2) ; CBV 2] #; *)
      (* Debug "p2:                    " p2 #; *)

      (* Call "init_with_fallback" [CBR p1 ; CBV p2] #; *)
      (* Debug "p1:                    " p1 #; *)
      (* Call "add_chunk" [CBR p1 ; CBV (big_chunk 1500 3) ; CBV 3] #; *)
      (* Debug "p1:                    " p1 #; *)

      (* Call "init_with_fallback" [CBR p0 ; CBV p1] #; *)
      (* Call "add_chunk" [CBR p0 ; CBV (big_chunk 500  1) ; CBV 1] #; *)
      (* Debug "p0:                    " p0 #; *)
      Call "mpool_init" [CBR p2] #;
      Call "init_with_fallback" [CBR p1 ; CBV p2] #;
      Call "init_with_fallback" [CBR p0 ; CBV p1] #;
      Call "add_chunk" [CBR p2 ; CBV (big_chunk 2500 2) ; CBV 2] #;
      Call "add_chunk" [CBR p1 ; CBV (big_chunk 1500 3) ; CBV 3] #;
      Call "add_chunk" [CBR p0 ; CBV (big_chunk 500  1) ; CBV 1] #;
      Debug "p2:                    " p2 #;
      Debug "p1:                    " p1 #;
      Debug "p0:                    " p0 #;



      Debug "" Vnull #;
      Debug "INIT DONE" Vnull #;
      Debug "" Vnull #;

      Debug "p0:                    " p0 #;
      r #= Call "alloc_contiguous" [CBR p0 ; CBV 1] #;
      #assume r #;
      Debug "p0:                    " p0 #;
      r #= Call "alloc_contiguous" [CBR p0 ; CBV 2] #;
      #assume r #;
      Debug "p0:                    " p0 #;
      r #= Call "alloc_contiguous" [CBR p0 ; CBV 3] #;
      #assume !r #;
      Debug "p0:                    " p0 #;
      r #= Call "alloc_contiguous" [CBR p0 ; CBV 2] #;
      #assume r #;
      Debug "p0:                    " p0 #;
      r #= Call "alloc_contiguous" [CBR p0 ; CBV 1] #;
      #assume r #;
      Debug "p0:                    " p0 #;
      r #= Call "alloc_contiguous" [CBR p0 ; CBV 1] #;
      #assume !r #;
      Put "Test3 Passed" Vnull #;
      Skip
    .
    Definition main1F: function.
      mk_function_tac main1 ([]: list var) ["p" ; "r1" ; "r2" ; "r3"]. Defined.

    Definition main2
               (p0 p1 p2 r: var): stmt :=
      p0 #= Vptr None [0: val ; 0: val ; 0: val ] #;
      p1 #= Vptr None [0: val ; 0: val ; 0: val ] #;
      p2 #= Vptr None [0: val ; 0: val ; 0: val ] #;
      Call "mpool_init" [CBR p2] #;
      Call "init_with_fallback" [CBR p1 ; CBV p2] #;
      Call "init_with_fallback" [CBR p0 ; CBV p1] #;
      Call "add_chunk" [CBR p0 ; CBV (big_chunk 500  1) ; CBV 1] #;
      Call "add_chunk" [CBR p1 ; CBV (big_chunk 1500 3) ; CBV 3] #;
      Call "add_chunk" [CBR p2 ; CBV (big_chunk 2500 2) ; CBV 2] #;
      Debug "p2:                    " p2 #;
      Debug "p1:                    " p1 #;
      Debug "p0:                    " p0 #;

      Debug "" Vnull #;
      Debug "INIT DONE" Vnull #;
      Debug "" Vnull #;

      Debug "p0:                    " p0 #;
      r #= Call "alloc_contiguous" [CBR p0 ; CBV 1] #;
      #assume r #;
      Debug "p0:                    " p0 #;
      r #= Call "alloc_contiguous" [CBR p0 ; CBV 2] #;
      #assume r #;
      Debug "p0:                    " p0 #;
      r #= Call "alloc_contiguous" [CBR p0 ; CBV 3] #;
      #assume (!r) #;
      Debug "p0:                    " p0 #;
      r #= Call "alloc_contiguous" [CBR p0 ; CBV 2] #;
      #assume r #;
      Debug "p0:                    " p0 #;
      r #= Call "alloc_contiguous" [CBR p0 ; CBV 1] #;
      #assume r #;
      Debug "p0:                    " p0 #;
      r #= Call "alloc_contiguous" [CBR p0 ; CBV 1] #;
      #assume (!r) #;
      Put "Test3 Passed" Vnull #;
      Skip
    .
    Definition main2F: function.
      mk_function_tac main2 ([]: list var) ["p" ; "r1" ; "r2" ; "r3"]. Defined.

    Definition program1: program :=
      [
        ("main", main1F) ;
          ("mpool_init", mpool_initF) ;
          ("init_with_fallback", init_with_fallbackF) ;
          ("alloc_contiguous", alloc_contiguousF) ;
          ("alloc_contiguous_no_fallback", alloc_contiguous_no_fallbackF) ;
          ("add_chunk", add_chunkF)
      ].
    Definition program2: program :=
      [
        ("main", main2F) ;
          ("mpool_init", mpool_initF) ;
          ("init_with_fallback", init_with_fallbackF) ;
          ("alloc_contiguous", alloc_contiguousF) ;
          ("alloc_contiguous_no_fallback", alloc_contiguous_no_fallbackF) ;
          ("add_chunk", add_chunkF)
      ].

    Definition isem1: itree Event unit :=
      eval_multimodule [program_to_ModSem program1 ; LOCK.modsem].
    Definition isem2: itree Event unit :=
      eval_multimodule [program_to_ModSem program2 ; LOCK.modsem].

  End TEST3.

  (****** TODO: move to Lang *****)
  Fixpoint INSERT_YIELD (s: stmt): stmt :=
    match s with
    | Seq s0 s1 => Seq (INSERT_YIELD s0) (INSERT_YIELD s1)
    | If c s0 s1 => If c (INSERT_YIELD s0) (INSERT_YIELD s1)
    | While c s => While c (INSERT_YIELD s)
    | _ => Yield #; s
    end
  .

  Module TEST4.

    Definition MAX: nat := 20.
    Definition pte_paddr_begin: N := 4000.

    Definition main (p i r: var): stmt := Eval compute in INSERT_YIELD (
      p #= Vptr None [0: val ; 0: val ; 0: val ] #;
      Call "mpool_init" [CBR p] #;
      DebugMpool "(Global Mpool) After initialize" p #;
      Call "add_chunk" [CBR p ; CBV (big_chunk pte_paddr_begin MAX) ; CBV (N.of_nat MAX)] #;
      "GMPOOL" #= p #;
      #while ("SIGNAL" <= 1) do (Debug "waiting for SIGNAL" Vnull) #;

      (*** JUST FOR PRINTING -- START ***)
      p #= (Call "Lock.acquire" [CBV (p #@ lock_ofs)]) #;
      DebugMpool "(Global Mpool) Final: " p #;
      (Call "Lock.release" [CBV (p #@ lock_ofs) ; CBV p]) #;
      (*** JUST FOR PRINTING -- END ***)

      i #= (N.of_nat MAX) #;
      #while i
      do (
        i #= i-1 #;
        r #= Call "alloc_contiguous" [CBR p ; CBV 1] #;
        #assume r
      ) #;
      Put "Test4 Passed" Vnull
    )
    .

    Definition alloc_and_free (sz: N)
               (p i r0 r1 r2: var): stmt := Eval compute in INSERT_YIELD (
      #while (! "GMPOOL") do (Debug "waiting for GMPOOL" Vnull) #;
      (* i #= MAX #; *)
      p #= Vptr None [0: val ; 0: val ; 0: val ] #;
      Call "init_with_fallback" [CBR p ; CBV "GMPOOL"] #;
      DebugMpool "(Local Mpool) After init-with-fallback" p #;
      (* #while i *)
      (* do ( *)
        Debug "looping, i is: " i #;
        i #= i - 1 #;
        r0 #= Call "alloc_contiguous" [CBR p ; CBV sz] #;
        r1 #= Call "alloc_contiguous" [CBR p ; CBV sz] #;
        r2 #= Call "alloc_contiguous" [CBR p ; CBV sz] #;
        #assume r0 #;
        #assume r1 #;
        #assume r2 #;
        Call "add_chunk" [CBR p ; CBV r0 ; CBV sz] #;
        Call "add_chunk" [CBR p ; CBV r1 ; CBV sz] #;
        Call "add_chunk" [CBR p ; CBV r2 ; CBV sz] #;
        Skip
      (* ) #; *)
      #;
      Call "fini" [CBR p] #;
      DebugMpool "(Local Mpool) After calling fini" p #;
      "SIGNAL" #= "SIGNAL" + 1 #;
      Skip
    )
    .

    Definition mainF: function.
      mk_function_tac main ([]: list var) ["p" ; "i" ; "r"]. Defined.
    Definition alloc_and_free2F: function.
      mk_function_tac (alloc_and_free 2) ([]: list var) ["p" ; "i" ; "r0" ; "r1" ; "r2"].
    Defined.
    Definition alloc_and_free3F: function.
      mk_function_tac (alloc_and_free 3) ([]: list var) ["p" ; "i" ; "r0" ; "r1" ; "r2"].
    Defined.

    Definition program: program :=
      [
        ("main", mainF) ;
          ("alloc_and_free2", alloc_and_free2F) ;
          ("alloc_and_free3", alloc_and_free3F) ;
          ("mpool_init", mpool_initF) ;
          ("init_with_fallback", init_with_fallbackF) ;
          ("fini", finiF) ;
          ("alloc_contiguous", alloc_contiguousF) ;
          ("alloc_contiguous_no_fallback", alloc_contiguous_no_fallbackF) ;
          ("add_chunk", add_chunkF)
      ].

    Definition modsems: list ModSem := [program_to_ModSem program ; LOCK.modsem].

    Definition isem: itree Event unit :=
      eval_multimodule_multicore
        modsems [ "main" ; "alloc_and_free2" ; "alloc_and_free3" ].

  End TEST4.

End TEST.

