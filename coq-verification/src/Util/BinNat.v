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
Require Import Coq.micromega.Lia.
Require Import Hafnium.Util.Tactics.
Local Open Scope N_scope.

(* TODO: organize this file; for instance, keep the lemmas about [shiftr] together *)
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
    N.land a (N.lnot (b - 1) (N.size a)) = a - a mod b.
  Admitted. (* TODO *)

  Lemma power_two_minus_1 n :
    is_power_of_two n ->
    n - 1 = N.ones (N.log2 n).
  Proof.
    cbv [is_power_of_two]; intros.
    rewrite N.ones_equiv. solver.
  Qed.

  Lemma land_ones' a b :
    is_power_of_two b ->
    N.land a (b - 1) = a mod (2 ^ N.log2 b).
  Proof.
    intros. rewrite power_two_minus_1 by auto.
    apply N.land_ones.
  Qed.

  Lemma power_two_trivial n :
    is_power_of_two (2 ^ n).
  Proof.
    cbv [is_power_of_two].
    rewrite N.log2_pow2; solver.
  Qed.

  Definition lt_le_dec n m : {n < m} + {m <= n}.
  Proof.
    destruct (N.eq_dec n m); [ right; solver | ].
    destruct (N.min_dec n m); [left | right ]; solver.
  Defined.

  Lemma mod_add_cancel_r a b : b <> 0 -> (a + b) mod b = a mod b.
  Proof.
    repeat match goal with
           | _ => progress basics
           | _ => rewrite N.mod_same by auto
           | _ => rewrite N.mod_mod by auto
           | _ => rewrite N.add_0_r
           | _ => rewrite (N.add_mod a b) by auto
           | _ => solver
           end.
  Qed.

  Lemma lt_pred_le a b : a < b -> a <= N.pred b.
  Proof. basics; solver. Qed.

  Lemma shiftr_le_mono_r a b n :
    (a <= b) -> N.shiftr a n <= N.shiftr b n.
  Proof.
    repeat match goal with
           | _ => progress basics
           | _ => rewrite N.shiftr_div_pow2
           | _ => apply N.div_le_mono
           | _ => apply N.pow_nonzero
           | _ => solver
           end.
  Qed.

  Lemma shiftr_lt_shiftl_mono a b n :
    a < (N.shiftl b n) -> N.shiftr a n < b.
  Proof.
    repeat match goal with
           | _ => progress basics
           | _ => rewrite N.shiftl_mul_pow2 in *
           | _ => rewrite N.shiftr_div_pow2
           | _ => apply N.div_lt_upper_bound
           | _ => apply N.pow_nonzero
           | _ => solver
           end.
  Qed.

  Lemma shiftl_inj_iff a b n :
    a = b <-> N.shiftl a n = N.shiftl b n.
  Proof.
    rewrite !N.shiftl_mul_pow2.
    rewrite N.mul_cancel_r by (apply N.pow_nonzero; solver).
    reflexivity.
  Qed.

  Lemma div_add_l' a b c :
    b <> 0 -> (b * a + c) / b = a + c / b.
  Proof. intros. rewrite (N.mul_comm b a). apply N.div_add_l; auto. Qed.

  Lemma mul_div a b : b <> 0 -> b * (a / b) = a - a mod b.
  Proof.
    (* TODO: this proof badly needs some autorewrite dbs *)
    intros.
    rewrite (N.div_mod a b) by auto.
    rewrite div_add_l' by auto.
    rewrite N.mul_add_distr_l.
    rewrite (N.div_small (_ mod _)) by (apply N.mod_bound_pos; solver).
    rewrite N.mul_0_r, N.add_0_r by auto.
    rewrite N.add_mod by auto.
    rewrite N.mul_mod by auto.
    rewrite N.mod_same by auto.
    rewrite N.mod_mod by auto.
    rewrite N.mul_0_l, N.mod_0_l, N.add_0_l by auto.
    rewrite N.mod_mod by auto.
    solver.
  Qed.

  Lemma mod_sub_small a b c :
    c <> 0 ->
    0 < a ->
    0 < b <= c ->
    (a * c - b) mod c = c - b.
  Proof.
    intros.
    assert (b <= a * c) by nia.
    transitivity ((a * c - b + c) mod c);
      [ rewrite N.add_mod, N.mod_same, N.add_0_r, N.mod_mod by solver;
        reflexivity | ].
    rewrite <-N.add_sub_swap by solver.
    rewrite <-N.add_sub_assoc by solver.
    rewrite N.add_mod, N.mod_mul, N.add_0_l, N.mod_mod by solver.
    rewrite !N.mod_small by solver.
    reflexivity.
  Qed.

  Lemma div_sub_small a b c :
    c <> 0 ->
    (0 < b <= c) ->
    (a * c - b) / c = a - 1.
  Proof.
    intros.
    destruct (N.eq_dec a 0); [ subst; solver | ].
    apply N.mul_cancel_l with (p:=c); [solver | ].
    rewrite mul_div by solver.
    rewrite mod_sub_small by solver.
    rewrite N.mul_sub_distr_l, N.mul_1_r.
    solver.
  Qed.

  Lemma div_between_eq a b c d :
    d <> 0 ->
    a <= b <= c ->
    a / d = c / d ->
    b / d = a / d.
  Proof.
    intros.
    match goal with
    | H : (?a / ?d = ?c / ?d) |- _ =>
      replace c with (d * (a / d) + (a mod d + (c - a))) in H
        by (rewrite N.add_assoc, <-N.div_mod; lia)
    end.
    replace b with (d * (a / d) + (a mod d + (b - a)))
      by (rewrite N.add_assoc, <-N.div_mod; lia).
    rewrite !div_add_l' in * by auto.
    assert ((a mod d + (c - a)) / d = 0) as Hdivsmall by lia.
    rewrite N.div_small_iff in Hdivsmall by auto.
    rewrite (N.div_small (_ + _)) by lia.
    lia.
  Qed.

  Lemma shiftr_add_shiftl a b n :
    N.shiftl (N.shiftr a n + b) n = a + N.shiftl b n - a mod (2 ^ n).
  Admitted.

End N.
Hint Resolve N.to_nat_lt_iff N.to_nat_le_iff.

Module Nat2N.
  Lemma inj_pow a b :
    N.of_nat (a ^ b) = N.of_nat a ^ N.of_nat b.
  Proof.
    induction b.
    { rewrite Nat.pow_0_r, N.pow_0_r. reflexivity. }
    { rewrite Nat.pow_succ_r by solver.
      rewrite Nnat.Nat2N.inj_succ.
      rewrite N.pow_succ_r by solver.
      rewrite Nnat.Nat2N.inj_mul.
      solver. }
  Qed.
End Nat2N.
