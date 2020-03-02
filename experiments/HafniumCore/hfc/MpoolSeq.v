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
Require Import Lang.
Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.



Set Implicit Arguments.




Module MPOOLSEQ.



  (* struct mpool { *)
  (* 	struct spinlock lock; *)
  (* 	size_t entry_size; *)
  (* 	struct mpool_chunk *chunk_list; *)
  (* 	struct mpool_entry *entry_list; *)
  (* 	struct mpool *fallback; *)
  (* }; *)



  (*
Simplified Mpool := Vptr [Vptr//chunk_list ; Vptr//fallback]
   *)

  Definition chunk_list_ofs := 0.
  Definition fallback_ofs := 1.
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

  Fixpoint mpool_wf (p: val): bool :=
    match p with
    | Vptr _ p =>
      match p with
      | [] => true
      | [chunk_list ; fallback] =>
        chunk_list_wf chunk_list && mpool_wf fallback
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

  Definition init (p: var): stmt :=
    (Store p chunk_list_ofs Vnull) #;
    (Store p fallback_ofs Vnull)
  .

  (* void mpool_init_with_fallback(struct mpool *p, struct mpool *fallback) *)
  (* { *)
  (* 	mpool_init(p, fallback->entry_size); *)
  (* 	p->fallback = fallback; *)
  (* } *)

  Definition init_with_fallback (p fallback: var): stmt :=
    Call "init" [CBR p] #;
    (Store p fallback_ofs fallback)
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

  (*** IGNORE THIS ***)
  Definition alloc_contiguous
             (p count: var)
             (ret: var): stmt :=
    #if (CoqCode [p: expr] (fun p => mpool_wf (nth 0 p Vnull)))
     then Skip
     else Guarantee
    #;
    #while Vtrue
     do (
       Debug "looping alloc_contiguous" Vnull #;
       ret #:= (Call "alloc_contiguous_no_fallback" [CBR p ; CBV count]) #;
       #if (ret)
       then (Return ret)
       else Skip
       #;
       p #:= (Load p fallback_ofs) #;
       #if (p)
       then Skip
       else Break
     ) #;
    Return Vnull
  .

  (*** DELTA: while -> recursion && call no_fallback with chunk_list, not mpool ***)
  Definition alloc_contiguous2
             (p count: var)
             (ret next nextp: var): stmt :=
    #if (CoqCode [p: expr] (fun p => mpool_wf (nth 0 p Vnull)))
     then Skip
     else Guarantee
    #;
    next #:= (Load p chunk_list_ofs) #;
    ret #:= (Call "alloc_contiguous_no_fallback2" [CBR next ; CBV count]) #;
    Store p chunk_list_ofs next #;
    #if (ret)
     then (Return ret)
     else (
         nextp #:= (Load p fallback_ofs) #;
         #if (! nextp) then Return Vnull else Skip #;
         (* Put "Looking inside fallback.." Vnull #; *)
         ret #:= (Call "alloc_contiguous2" [CBR nextp ; CBV count]) #;
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

  (*** IGNORE THIS ***)
  Definition alloc_contiguous_no_fallback
             (p count: var)
             (prev ret new_chunk chunk: var): stmt :=
    #if (CoqCode [p: expr] (fun p => mpool_wf (nth 0 p Vnull)))
     then Skip
     else Guarantee
    #;
    prev #:= (#& (Load p chunk_list_ofs)) #;
    Debug "(A)prev_is: " prev #;
    #while prev
     do (
       chunk #:= (#* prev) #;
       new_chunk #:= (SubPointerFrom chunk (count * entry_size)) #;
       (* if (new_chunk <= chunk->limit) *)
       (* #if new_chunk *)
       #if (count <= (Load chunk limit_ofs))
        then
          (
           (Debug "If1-limit: " (Load chunk limit_ofs)) #;
           #if count == (Load chunk limit_ofs)
            then (
                Store prev 0 (Load chunk next_chunk_ofs) (** should write to p **)
              )
            else (
                Store new_chunk next_chunk_ofs (Load chunk next_chunk_ofs) #;
                Store new_chunk limit_ofs (Load chunk limit_ofs) #;
                Store prev 0 new_chunk
              )
           #;
           (* ret = (void * )start; *) (** code doesn't specify the size, but we need too **)
           Debug "(A)chunk_is: " chunk #;
           ret #:= (SubPointerTo chunk (count * entry_size)) #;
           Debug "(A)ret_is: " ret #;
           Break
          )
        else
          (
            (Debug "Else1-limit: " (Load chunk limit_ofs)) #;
            (prev #:= #& (Load chunk next_chunk_ofs)) #;
            (Debug "Else1-prev: " prev) #;
            Skip
          )
     ) #;
    Debug "no_fallback returns: " ret #;
    Return ret
  .

  (*** DELTA: while -> recursion && "limit" ptr -> offset "nat" && no alignment ***)
  Definition alloc_contiguous_no_fallback2
             (cur count: var)
             (ret next cur_ofs new_cur: var): stmt :=
    #if ! cur then Return Vnull else Skip #;
    cur_ofs #:= (Load cur limit_ofs) #;
    #if (count <= cur_ofs)
     then (
           (* (Debug "If-limit: " cur_ofs) #; *)
           #if count == cur_ofs
            then (
                (* (Debug "If-If: " Vnull) #; *)
                ret #:= (SubPointerTo cur (count * entry_size)) #;
                cur #:= (Load cur next_chunk_ofs) #;
                Return ret
              )
            else (
                (* (Debug "If-Else: " Vnull) #; *)
                new_cur #:= (SubPointerFrom cur (count * entry_size)) #;
                Store new_cur next_chunk_ofs (Load cur next_chunk_ofs) #;
                Store new_cur limit_ofs (cur_ofs - count) #;
                ret #:= (SubPointerTo cur (count * entry_size)) #;
                cur #:= new_cur #;
                Return ret
              )
          )
     else (
         (* (Debug "Else-limit: " cur_ofs) #; *)
         next #:= (Load cur next_chunk_ofs) #;
         ret #:= (Call "alloc_contiguous_no_fallback2" [CBR next ; CBV count]) #;
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

    Store chunk next_chunk_ofs (Load p chunk_list_ofs) #;
    Store p chunk_list_ofs chunk
  .

  Definition initF: function :=
    mk_function ["p"] (init "p").
  Definition init_with_fallbackF: function :=
    mk_function ["p" ; "fb"] (init_with_fallback "p" "fb").
  Definition alloc_contiguousF: function :=
    mk_function ["p" ; "count"] (alloc_contiguous "p" "count" "ret").
  Definition alloc_contiguous_no_fallbackF: function :=
    mk_function ["p" ; "count"]
                (alloc_contiguous_no_fallback "p" "count" "prev" "ret" "new_chunk" "chunk").
  Definition alloc_contiguous2F: function :=
    mk_function ["p" ; "count"] (alloc_contiguous2 "p" "count" "ret" "next" "nextp").
  Definition alloc_contiguous_no_fallback2F: function :=
    mk_function ["cur" ; "count"]
                (alloc_contiguous_no_fallback2 "cur" "count" "ret" "next"
                                               "cur_ofs" "new_cur").
  Definition add_chunkF: function :=
    mk_function ["p" ; "begin" ; "size"] (add_chunk "p" "begin" "size" "chunk").

End MPOOLSEQ.



Module TEST.

  Include MPOOLSEQ.

  Definition big_chunk (paddr: nat) (size: nat): val :=
    Vptr (Some paddr) (repeat (Vnat 0) (entry_size * size)).

  Module TEST1.

    Definition main
               (p r1 r2 r3: var): stmt :=
      p #:= Vptr None [0: val ; 0: val] #;
        (Put "before init: " p) #;
        Call "init" [CBR p] #;
        (Put "after init: " p) #;
        Call "add_chunk" [CBR p ; CBV (big_chunk 500 10) ; CBV 10] #;
        (Put "add_chunk done: " p) #;

        r1 #:= Call "alloc_contiguous" [CBR p ; CBV 7] #;
        (Put "alloc first; should succeed: " r1) #;
        (Put "alloc first; p: " p) #;

        r2 #:= Call "alloc_contiguous" [CBR p ; CBV 7] #;
        (Put "alloc second; should fail: " r2) #;
        (Put "alloc second; p: " p) #;

        Call "add_chunk" [CBR p ; CBV r1 ; CBV 7] #;
        (Put "add_chunk done" p) #;

        r3 #:= Call "alloc_contiguous" [CBR p ; CBV 7] #;
        (Put "alloc third; should succeed: " r3) #;
        (Put "alloc third; p: " p) #;
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

  End TEST1.



  Module TEST2.

    Definition main
               (p r1 r2 r3: var): stmt :=
      p #:= Vptr None [0: val ; 0: val] #;
        (* (Put "before init: " p) #; *)
        Call "init" [CBR p] #;
        (* (Put "after init: " p) #; *)
        Call "add_chunk" [CBR p ; CBV (big_chunk 500 10) ; CBV 10] #;
        (* (Put "add_chunk done: " p) #; *)

        r1 #:= Call "alloc_contiguous2" [CBR p ; CBV 7] #;
        (* (Put "alloc first; should succeed: " r1) #; *)
        (* (Put "alloc first; p: " p) #; *)
        #if r1 then Skip else Assume #;

        r2 #:= Call "alloc_contiguous2" [CBR p ; CBV 7] #;
        (* (Put "alloc second; should fail: " r2) #; *)
        (* (Put "alloc second; p: " p) #; *)
        #if r2 then Assume else Skip #;

        Call "add_chunk" [CBR p ; CBV r1 ; CBV 7] #;
        (* (Put "add_chunk done" p) #; *)

        r3 #:= Call "alloc_contiguous2" [CBR p ; CBV 7] #;
        (* (Put "alloc third; should succeed: " r3) #; *)
        (* (Put "alloc third; p: " p) #; *)
        #if r3 then Skip else Assume #;


        Put "Test2 Passed" Vnull #;
        Skip
    .
    Definition mainF: function := mk_function [] (main "p" "r1" "r2" "r3").

    Definition program: program :=
      [
        ("main", mainF) ;
          ("init", initF) ;
          ("alloc_contiguous2", alloc_contiguous2F) ;
          ("alloc_contiguous_no_fallback2", alloc_contiguous_no_fallback2F) ;
          ("add_chunk", add_chunkF)
      ].

  End TEST2.







  Module TEST3.

    Definition main
               (p r1 r2 r3: var): stmt :=
      p #:= Vptr None [0: val ; 0: val] #;
        (* (Put "before init: " p) #; *)
        Call "init" [CBR p] #;
        (* (Put "after init: " p) #; *)
        Call "add_chunk" [CBR p ; CBV (big_chunk 500 10) ; CBV 10] #;
        Call "add_chunk" [CBR p ; CBV (big_chunk 1500 10) ; CBV 10] #;
        (* (Put "add_chunk done: " p) #; *)

        r1 #:= Call "alloc_contiguous2" [CBR p ; CBV 7] #;
        (* (Put "alloc first; should succeed: " r1) #; *)
        (* (Put "alloc first; p: " p) #; *)
        #if r1 then Skip else Assume #;

        r2 #:= Call "alloc_contiguous2" [CBR p ; CBV 7] #;
        (* (Put "alloc second; should succeed: " r2) #; *)
        (* (Put "alloc second; p: " p) #; *)
        #if r2 then Skip else Assume #;

        Put "Test3 Passed" Vnull #;
        Skip
    .
    Definition mainF: function := mk_function [] (main "p" "r1" "r2" "r3").

    Definition program: program :=
      [
        ("main", mainF) ;
          ("init", initF) ;
          ("alloc_contiguous2", alloc_contiguous2F) ;
          ("alloc_contiguous_no_fallback2", alloc_contiguous_no_fallback2F) ;
          ("add_chunk", add_chunkF)
      ].

  End TEST3.





  Module TEST4.

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
      p0 #:= Vptr None [0: val ; 0: val] #;
      p1 #:= Vptr None [0: val ; 0: val] #;
      p2 #:= Vptr None [0: val ; 0: val] #;
      Call "init" [CBR p2] #;
      Call "add_chunk" [CBR p2 ; CBV (big_chunk 2500 2) ; CBV 2] #;

      Call "init_with_fallback" [CBR p1 ; CBV p2] #;
      Call "add_chunk" [CBR p1 ; CBV (big_chunk 1500 3) ; CBV 3] #;

      Call "init_with_fallback" [CBR p0 ; CBV p1] #;
      Call "add_chunk" [CBR p0 ; CBV (big_chunk 500  1) ; CBV 1] #;
      

      r #:= Call "alloc_contiguous2" [CBR p0 ; CBV 1] #;
      #if r then Skip else Assume #;
      r #:= Call "alloc_contiguous2" [CBR p0 ; CBV 2] #;
      #if r then Skip else Assume #;
      r #:= Call "alloc_contiguous2" [CBR p0 ; CBV 3] #;
      #if r then Assume else Skip #;
      r #:= Call "alloc_contiguous2" [CBR p0 ; CBV 2] #;
      #if r then Skip else Assume #;
      r #:= Call "alloc_contiguous2" [CBR p0 ; CBV 1] #;
      #if r then Skip else Assume #;
      r #:= Call "alloc_contiguous2" [CBR p0 ; CBV 1] #;
      #if r then Assume else Skip #;
      Put "Test4 Passed" Vnull #;
      Skip
    .
    Definition mainF: function := mk_function [] (main "p0" "p1" "p2" "r").

    Definition program: program :=
      [
        ("main", mainF) ;
          ("init", initF) ;
          ("init_with_fallback", init_with_fallbackF) ;
          ("alloc_contiguous2", alloc_contiguous2F) ;
          ("alloc_contiguous_no_fallback2", alloc_contiguous_no_fallback2F) ;
          ("add_chunk", add_chunkF)
      ].

  End TEST4.






  Module PROPSINGLE.
    Module MATH.
      Definition mpool := list (list nat).
      Definition add_chunk (p: mpool) (c: nat): mpool :=
        match p with
        | hd :: tl => (cons c hd) :: tl
        | _ => [] (** SHOULD NOT HAPPEN *)
        end
      .
      Fixpoint alloc_contiguous_no_fallback (p: list nat) (c: nat): option (list nat) :=
        match p with
        | [] => None
        | hd :: tl => if c <? hd
                      then Some ((hd - c)%nat :: tl)
                      else if (c =? hd)%nat
                           then Some tl
                           else alloc_contiguous_no_fallback tl c
        end
      .
      Fixpoint alloc_contiguous (p: mpool) (c: nat): option mpool :=
        match p with
        | [] => None
        | hd :: tl =>
          match alloc_contiguous_no_fallback hd c with
          | Some hd => Some (hd :: tl)
          | None =>
            match alloc_contiguous tl c with
            | Some tl => Some (hd :: tl)
            | None => None
            end
          end
        end
      .
    End MATH.

    Definition random_range (n: nat): nat := 0.
    Definition random_latest: nat := 0.

    Definition main
               (p0 p1 p2 q tmp0 tmp1: var): stmt :=
      p0 #:= Vptr None [0: val ; 0: val] #;
      p1 #:= Vptr None [0: val ; 0: val] #;
      p2 #:= Vptr None [0: val ; 0: val] #;
      Call "init" [CBR p0] #;
      Call "init_with_fallback" [CBR p1 ; CBV p0] #;
      Call "init_with_fallback" [CBR p2 ; CBV p1] #;

      #while Vtrue
      do (
        #if ((CoqCode [] (fun _ => random_range 2)) == 0)
         then
           (* add_chunk *)
           tmp0 #:= (CoqCode [] (fun _ => random_range 3)) #;
           tmp1 #:= (CoqCode [] (fun _ => random_range 10)) #;
           (#if (tmp0 == 0)
             then Call "add_chunk" [CBR p0 ; CBV (big_chunk 0 random_latest) ; CBV tmp1]
             else
           (#if (tmp0 == 1)
             then Call "add_chunk" [CBR p1 ; CBV (big_chunk 0 random_latest) ; CBV tmp1]
             else
           (#if (tmp0 == 2)
             then Call "add_chunk" [CBR p2 ; CBV (big_chunk 0 random_latest) ; CBV tmp1]
             else Guarantee)))
         else
           (* alloc_continuous *)
           Skip
      )
    .

    (* Definition mainF: function := mk_function [] (main "p" "r1" "r2" "r3"). *)

    (* Definition program: program := *)
    (*   [ *)
    (*     ("main", mainF) ; *)
    (*       ("init", initF) ; *)
    (*       ("init_with_fallback", init_with_fallbackF) ; *)
    (*       ("alloc_contiguous2", alloc_contiguous2F) ; *)
    (*       ("alloc_contiguous_no_fallback2", alloc_contiguous_no_fallback2F) ; *)
    (*       ("add_chunk", add_chunkF) *)
    (*   ]. *)

  End PROPSINGLE.



End TEST.


