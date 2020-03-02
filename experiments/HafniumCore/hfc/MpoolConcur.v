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
Local Open Scope expr_scope.
Local Open Scope stmt_scope.



Set Implicit Arguments.





Module MPOOLCONCUR.

  (*
Simplified Mpool := Vptr [Vnat//lock ; Vptr//chunk_list ; Vptr//fallback]
   *)

  Definition lock_ofs := 0.
  Definition chunk_list_ofs := 1.
  Definition fallback_ofs := 2.
  Definition next_chunk_ofs := 0.
  Definition limit_ofs := 1.

  Definition entry_size: nat := 4.

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
          if Nat.eq_dec (length cts) (limit * entry_size)
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

  (*** DELTA: Use function return value instead of borrowing && Add call to "Lock.unlock" **)
  Definition init (p: var): stmt :=
    (Store p chunk_list_ofs Vnull) #;
    (Store p fallback_ofs Vnull) #;
    (Store p lock_ofs (Call "Lock.new" [])) #;
    (Call "Lock.unlock" [CBV (Load p lock_ofs) ; CBV p]) #;
    Skip
  .

  (* void mpool_init_with_fallback(struct mpool *p, struct mpool *fallback) *)
  (* { *)
  (* 	mpool_init(p, fallback->entry_size); *)
  (* 	p->fallback = fallback; *)
  (* } *)

  (*** DELTA: Add call to "Lock.unlock"  ***)
  Definition init_with_fallback (p fallback: var): stmt :=
    (* Call "init" [CBR p] #; *)
    (* (Store p fallback_ofs fallback) #; *)
    (* (Call "Lock.unlock" [CBV (Load p lock_ofs) ; CBV p]) #; *)
    (Store p chunk_list_ofs Vnull) #;
    (Store p fallback_ofs fallback) #;
    (Store p lock_ofs (Call "Lock.new" [])) #;
    (Call "Lock.unlock" [CBV (Load p lock_ofs) ; CBV p]) #;
    Skip
  .

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
    #if (CoqCode [p: expr] (fun p => mpool_wf (nth 0 p Vnull)))
     then Skip
     else Guarantee
    #;
    p #:= (Call "Lock.lock" [CBV (Load p lock_ofs)]) #;
    next #:= (Load p chunk_list_ofs) #;
    ret #:= (Call "alloc_contiguous_no_fallback" [CBR next ; CBV count]) #;
    Store p chunk_list_ofs next #;
    (Call "Lock.unlock" [CBV (Load p lock_ofs) ; CBV p]) #;
    #if (ret)
     then (Return ret)
     else (
         nextp #:= (Load p fallback_ofs) #;
         #if (! nextp) then Return Vnull else Skip #;
         ret #:= (Call "alloc_contiguous" [CBR nextp ; CBV count]) #;
         (Store p fallback_ofs nextp) #;
         Return ret
       )
  .

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
    cur_ofs #:= (Load cur limit_ofs) #;
    #if (count <= cur_ofs)
     then (
           (Debug "If1-limit: " cur_ofs) #;
           #if count == cur_ofs
            then (
                ret #:= (SubPointerTo cur (count * entry_size)) #;
                cur #:= (Load cur next_chunk_ofs) #;
                Return ret
              )
            else (
                new_cur #:= (SubPointerFrom cur (count * entry_size)) #;
                Store new_cur next_chunk_ofs (Load cur next_chunk_ofs) #;
                Store new_cur limit_ofs (cur_ofs - count) #;
                ret #:= (SubPointerTo cur (count * entry_size)) #;
                cur #:= new_cur #;
                Return ret
              )
          )
     else (
         (Debug "Else1-limit: " cur_ofs) #;
         next #:= (Load cur next_chunk_ofs) #;
         ret #:= (Call "alloc_contiguous_no_fallback" [CBR next ; CBV count]) #;
         Store cur next_chunk_ofs next #;
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
    chunk #:= begin #;
    (* Store chunk limit_ofs ((GetLen chunk) / entry_size) #; *)
    Store chunk limit_ofs size #;

    Debug "add_chunk-calling lock" p #;
    p #:= (Call "Lock.lock" [CBV (Load p lock_ofs)]) #;
    Store chunk next_chunk_ofs (Load p chunk_list_ofs) #;
    Store p chunk_list_ofs chunk #;
    (Call "Lock.unlock" [CBV (Load p lock_ofs) ; CBV p]) #;
    Skip
  .

  Definition initF: function :=
    mk_function ["p"] (init "p").
  Definition init_with_fallbackF: function :=
    mk_function ["p" ; "fb"] (init_with_fallback "p" "fb").
  Definition alloc_contiguousF: function :=
    mk_function ["p" ; "count"] (alloc_contiguous "p" "count" "ret" "next" "nextp").
  Definition alloc_contiguous_no_fallbackF: function :=
    mk_function ["cur" ; "count"]
                (alloc_contiguous_no_fallback "cur" "count" "ret" "next"
                                              "cur_ofs" "new_cur").
  Definition add_chunkF: function :=
    mk_function ["p" ; "begin" ; "size"] (add_chunk "p" "begin" "size" "chunk").


End MPOOLCONCUR.
























Module TEST.

  Include MPOOLCONCUR.

  Definition big_chunk (paddr: nat) (size: nat): val :=
    Vptr (Some paddr) (repeat (Vnat 0) (entry_size * size)).

  Module TEST1.

    Definition main
               (p r1 r2 r3: var): stmt :=
      p #:= Vptr None [0: val ; 0: val ; 0: val] #;
        (* (Put "before init: " p) #; *)
        Debug "before init: " p #;
        Call "init" [CBR p] #;
        Debug "after init: " p #;
        Call "add_chunk" [CBR p ; CBV (big_chunk 500 10) ; CBV 10] #;
        (* (Put "add_chunk done: " p) #; *)
        Debug "add_chunk done: " p #;

        r1 #:= Call "alloc_contiguous" [CBR p ; CBV 7] #;
        (* (Put "alloc first; should succeed: " r1) #; *)
        (* (Put "alloc first; p: " p) #; *)
        Debug "alloc_contiguous done: " p #;
        #if r1 then Skip else Assume #;

        r2 #:= Call "alloc_contiguous" [CBR p ; CBV 7] #;
        (* (Put "alloc second; should fail: " r2) #; *)
        (* (Put "alloc second; p: " p) #; *)
        Debug "alloc_contiguous done: " p #;
        #if r2 then Assume else Skip #;

        Call "add_chunk" [CBR p ; CBV r1 ; CBV 7] #;
        (* (Put "add_chunk done" p) #; *)

        r3 #:= Call "alloc_contiguous" [CBR p ; CBV 7] #;
        (* (Put "alloc third; should succeed: " r3) #; *)
        (* (Put "alloc third; p: " p) #; *)
        #if r3 then Skip else Assume #;


        Put "Test1 Passed" Vnull #;
        Skip
    .
    Definition mainF: function := mk_function [] (main "p" "r1" "r2" "r3").

    Definition program: program :=
      [
        ("main", mainF) ;
          ("init", initF) ;
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
      p #:= Vptr None [0: val ; 0: val ; 0: val ] #;
        (* (Put "before init: " p) #; *)
        Call "init" [CBR p] #;
        (* (Put "after init: " p) #; *)
        Call "add_chunk" [CBR p ; CBV (big_chunk 500 10) ; CBV 10] #;
        Call "add_chunk" [CBR p ; CBV (big_chunk 1500 10) ; CBV 10] #;
        (* (Put "add_chunk done: " p) #; *)

        r1 #:= Call "alloc_contiguous" [CBR p ; CBV 7] #;
        (* (Put "alloc first; should succeed: " r1) #; *)
        (* (Put "alloc first; p: " p) #; *)
        #if r1 then Skip else Assume #;

        r2 #:= Call "alloc_contiguous" [CBR p ; CBV 7] #;
        (* (Put "alloc second; should succeed: " r2) #; *)
        (* (Put "alloc second; p: " p) #; *)
        #if r2 then Skip else Assume #;

        Put "Test2 Passed" Vnull #;
        Skip
    .
    Definition mainF: function := mk_function [] (main "p" "r1" "r2" "r3").

    Definition program: program :=
      [
        ("main", mainF) ;
          ("init", initF) ;
          ("alloc_contiguous", alloc_contiguousF) ;
          ("alloc_contiguous_no_fallback", alloc_contiguous_no_fallbackF) ;
          ("add_chunk", add_chunkF)
      ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem program ; LOCK.modsem].

  End TEST2.





  Module TEST3.

    Definition main
               (p0 p1 p2 r: var): stmt :=
      (* p0 #:= Vptr None [0: val ; 0: val] #; *)
      (* p1 #:= Vptr None [0: val ; 0: val] #; *)
      (* p2 #:= Vptr None [0: val ; 0: val] #; *)
      (* Call "init" [CBR p2] #; *)
      (* Call "init_with_fallback" [CBR p1 ; CBV p2] #; *)
      (* Call "init_with_fallback" [CBR p0 ; CBV p1] #; *)
      
      (* Call "add_chunk" [CBR p0 ; CBV (big_chunk 500  5 ) ; CBV  5] #; *)
      (* Call "add_chunk" [CBR p1 ; CBV (big_chunk 1500 15) ; CBV 15] #; *)
      (* Call "add_chunk" [CBR p2 ; CBV (big_chunk 2500 10) ; CBV 10] #; *)

      (* r #:= Call "alloc_contiguous2" [CBR p0 ; CBV 5] #; *)
      (* #if r then Skip else Assume #; *)
      (* Call "alloc_contiguous2" [CBR p0 ; CBV 10] #; *)
      (* #if r then Skip else Assume #; *)
      (* Call "alloc_contiguous2" [CBR p0 ; CBV 15] #; *)
      (* #if r then Assume else Skip #; *)
      (* Call "alloc_contiguous2" [CBR p0 ; CBV 5] #; *)
      (* #if r then Skip else Assume #; *)
      (* Call "alloc_contiguous2" [CBR p0 ; CBV 10] #; *)
      (* #if r then Skip else Assume #; *)
      (* Call "alloc_contiguous2" [CBR p0 ; CBV 5] #; *)
      (* #if r then Skip else Assume #; *)
      (* Skip *)
      p0 #:= Vptr None [0: val ; 0: val ; 0: val ] #;
      p1 #:= Vptr None [0: val ; 0: val ; 0: val ] #;
      p2 #:= Vptr None [0: val ; 0: val ; 0: val ] #;
      Call "init" [CBR p2] #;
      Call "add_chunk" [CBR p2 ; CBV (big_chunk 2500 2) ; CBV 2] #;
      Debug "p2:                    " p2 #;

      Call "init_with_fallback" [CBR p1 ; CBV p2] #;
      Debug "p1:                    " p1 #;
      Call "add_chunk" [CBR p1 ; CBV (big_chunk 1500 3) ; CBV 3] #;
      Debug "p1:                    " p1 #;

      Call "init_with_fallback" [CBR p0 ; CBV p1] #;
      Call "add_chunk" [CBR p0 ; CBV (big_chunk 500  1) ; CBV 1] #;
      Debug "p0:                    " p0 #;


      Debug "" Vnull #;
      Debug "INIT DONE" Vnull #;
      Debug "" Vnull #;

      Debug "p0:                    " p0 #;
      r #:= Call "alloc_contiguous" [CBR p0 ; CBV 1] #;
      #if r then Skip else Assume #;
      Debug "p0:                    " p0 #;
      r #:= Call "alloc_contiguous" [CBR p0 ; CBV 2] #;
      #if r then Skip else Assume #;
      Debug "p0:                    " p0 #;
      r #:= Call "alloc_contiguous" [CBR p0 ; CBV 3] #;
      #if r then Assume else Skip #;
      Debug "p0:                    " p0 #;
      r #:= Call "alloc_contiguous" [CBR p0 ; CBV 2] #;
      #if r then Skip else Assume #;
      Debug "p0:                    " p0 #;
      r #:= Call "alloc_contiguous" [CBR p0 ; CBV 1] #;
      #if r then Skip else Assume #;
      Debug "p0:                    " p0 #;
      r #:= Call "alloc_contiguous" [CBR p0 ; CBV 1] #;
      #if r then Assume else Skip #;
      Put "Test3 Passed" Vnull #;
      Skip
    .
    Definition mainF: function := mk_function [] (main "p0" "p1" "p2" "r").

    Definition program: program :=
      [
        ("main", mainF) ;
          ("init", initF) ;
          ("init_with_fallback", init_with_fallbackF) ;
          ("alloc_contiguous", alloc_contiguousF) ;
          ("alloc_contiguous_no_fallback", alloc_contiguous_no_fallbackF) ;
          ("add_chunk", add_chunkF)
      ].

    Definition isem: itree Event unit :=
      eval_multimodule [program_to_ModSem program ; LOCK.modsem].

  End TEST3.



End TEST.




