(*
 * Copyright 2019 Jade Philipoom
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

Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.
Require Import Hafnium.Util.Tactics.
Local Open Scope N_scope.

Module N.
  Lemma to_nat_ltb (x y : N) :
    (x <? y)%N = (N.to_nat x <? N.to_nat y)%nat.
  Proof.
    rewrite N.ltb_compare, Nat.ltb_compare.
    rewrite N2Nat.inj_compare.
    reflexivity.
  Qed.

  Lemma to_nat_le_iff (x y : N) :
    (N.to_nat x <= N.to_nat y)%nat <-> x <= y.
  Proof.
    rewrite <-N.compare_le_iff, <-Nat.compare_le_iff.
    rewrite N2Nat.inj_compare. reflexivity.
  Qed.

  Lemma to_nat_lt_iff x y : (N.to_nat x < N.to_nat y)%nat <-> x < y.
  Admitted. (* TODO *)

  Lemma div2_lnot a n : N.div2 (N.lnot a n) = N.lnot (N.div2 a) (N.pred n).
  Admitted. (* TODO *)

  Lemma lnot_shiftr a n m :
    N.shiftr (N.lnot a n) m = N.lnot (N.shiftr a m) (n - m).
  Proof.
    rewrite <-(Nnat.N2Nat.id m).
    induction (N.to_nat m).
    { rewrite !N.shiftr_0_r.
      rewrite N.sub_0_r. reflexivity. }
    { rewrite Nnat.Nat2N.inj_succ.
      rewrite !N.shiftr_succ_r.
      rewrite N.sub_succ_r.
      rewrite <-div2_lnot.
      solver. }
  Qed.

  Lemma log2_add_shiftl_1 a b : b <= N.log2 (a + (N.shiftl 1 b)).
  Admitted. (* TODO *)

  Definition is_power_of_two (n : N) : Prop := n = N.pow 2 (N.log2 n).

  Lemma power_two_pos (n : N) :
    is_power_of_two n ->
    (0 < n)%N.
  Proof.
    cbv [is_power_of_two]; intro H; rewrite H.
    apply N.lt_le_trans with (m:=2 ^ 0);
      [ rewrite N.pow_0_r; solver | ].
    apply N.pow_le_mono_r;
      auto using N.log2_nonneg; solver.
  Qed.

  Lemma shiftl_power_two n :
    is_power_of_two (N.shiftl 1 n).
  Proof.
    cbv [is_power_of_two].
    rewrite N.shiftl_1_l, N.log2_pow2 by solver.
    reflexivity.
  Qed.

  Lemma and_not a b :
    is_power_of_two b ->
    (N.land a (N.lnot (b - 1) (N.size a)) = a - a mod b)%N.
  Admitted.
End N.
