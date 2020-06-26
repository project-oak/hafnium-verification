(*
 * Copyright 2020 Jieung Kim (jieungkim@google.com)
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
(*
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
Require Import TestAux.
Require Import Lang.
Require Import Types.
Require Import MpoolConcur.
Require Import ArchMM.
Require Import Lock.

Import LangNotations.
Local Open Scope expr_scope.
Local Open Scope stmt_scope.

Section MMSTAGE1.
  
  (*
  static struct mm_page_table *mm_alloc_page_tables(size_t count,
                                                    struct mpool *ppool)
  {
          if (count == 1) {
                  return mpool_alloc(ppool);
          }

          return mpool_alloc_contiguous(ppool, count, count);
  }
  *)
  
  Definition mm_alloc_page_tables (count ppool: var) (res : var) : stmt :=
    #if (count == 1)
     then
       res #= (Call "mpool_alloc" [CBR ppool]) #;
           Return res
     else
       res #= (Call "mpool_alloc_contiguous" [CBR ppool ; CBV count ; CBV count]) #;
           Return res.
  

End MMSTAGE1.


Module TEST.

(*
NOTICE: Initialising hafnium
INFO: text: 0x40001000 - 0x40018000
INFO: rodata: 0x40018000 - 0x4001b000
INFO: data: 0x4001b000 - 0x400b3000
INFO: Supported bits in physical address: 44
INFO: Stage 2 has 4 page table levels with 1 pages at the root.
INFO: Found PSCI version: 0x2
ERROR: Unable to read linux,initrd-start
Panic: Could not parse boot params. 
*)


End TEST.




(*

  Module TEST4.

    Definition MAX: nat := 20.
    Definition pte_paddr_begin: nat := 4000.

    Definition main (p i r: var): stmt := Eval compute in INSERT_YIELD (
      p #= Vptr None [0: val ; 0: val ; 0: val ] #;
      Call "init" [CBR p] #;
      DebugMpool "(Global Mpool) After initialize" p #;
      Call "add_chunk" [CBR p ; CBV (big_chunk pte_paddr_begin MAX) ; CBV MAX] #;
      "GMPOOL" #= p #;
      #while ("SIGNAL" <= 1) do (Debug "waiting for SIGNAL" Vnull) #;

      (*** JUST FOR PRINTING -- START ***)
      p #= (Call "Lock.acquire" [CBV (p #@ lock_ofs)]) #;
      DebugMpool "(Global Mpool) Final: " p #;
      (Call "Lock.release" [CBV (p #@ lock_ofs) ; CBV p]) #;
      (*** JUST FOR PRINTING -- END ***)

      i #= MAX #;
      #while i
      do (
        i #= i-1 #;
        r #= Call "alloc_contiguous" [CBR p ; CBV 1] #;
        #assume r
      ) #;
      Put "Test4 Passed" Vnull
    )
    .

    Definition alloc_and_free (sz: nat)
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
          ("init", initF) ;
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

*)
*)
