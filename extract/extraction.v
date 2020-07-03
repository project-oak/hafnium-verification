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
Require Extraction.

(* From HafniumCore *)
(* YJ: Having some makefile problem. (dependency checking) need to solve that !! *)
Require Import Lang LangTest.
Require Import MpoolSeq MpoolConcur CPUSeq MM MMStageOne MMHighStageOne.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
(* Require Import ExtrOcamlNatInt. *)

(* Avoid name clashes *)
Extraction Blacklist List String Int.

Cd "extract".

(*** TODO: I just want to write as below, but it does NOT work!!!!! ***)
(* Separate Extraction MpoolSeq MpoolConcur Lang LangTest. *)

Separate Extraction
         Any.string_of_Any
         Lang.eval_whole_program
         Lang.eval_single_program
         Lang.Vtrue
         Lang.Vfalse
         LangTest.LoadStore.program
         LangTest.Rec.program
         LangTest.MutRec.program
         LangTest.Move.program
         LangTest.CoqCode.program
         LangTest.CoqCodeCBR.isem
         LangTest.Control.program
         LangTest.DoubleReturn.program
         LangTest.MultiCore.programs
         LangTest.MultiCore2.sem
         LangTest.MultiCoreMPSC.sem
         LangTest.MultiModule.isem
         LangTest.MultiModuleGenv.isem
         LangTest.MultiModuleLocalState.isem
         LangTest.MultiModuleLocalStateSimple.isem1
         LangTest.MultiModuleLocalStateSimple.isem2
         LangTest.MultiModuleLocalStateSimpleLang.isem
         LangTest.MultiModuleMultiCore.sem
         LangTest.MultiModuleMultiCoreLocalState.isem
         LangTest.PrintAny.isem
         (* LangTest.print_val *)
         (* LangTest.main *)
         (* LangTest.handle_Event *)
         (* LangTest.cl2s *)

         MpoolSeq.TEST.TEST1.program
         MpoolSeq.TEST.TEST2.program
         MpoolSeq.TEST.TEST3.program
         MpoolSeq.TEST.TEST4.program

         MpoolConcur.TEST.TEST1.isem
         MpoolConcur.TEST.TEST2.isem
         MpoolConcur.TEST.TEST3.isem1
         MpoolConcur.TEST.TEST3.isem2
         MpoolConcur.TEST.TEST4.isem

         CPUSeq.CPUTEST.program

         MMStageOne.MMTEST1.isem


         MMHighStageOne.HighSpecDummyTest.program
         
         Lang.round_robin
         Lang.run_till_yield
         Lang.my_rr_match
         
         ITreeDefinition.observe
.

Cd "..".
