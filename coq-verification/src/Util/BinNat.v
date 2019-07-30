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

(* autorewrite databases for converting from nat to N and back *)
Hint Rewrite N2Nat.id Nat2N.id N2Nat.inj N2Nat.inj_add N2Nat.inj_mul
     N2Nat.inj_max N2Nat.inj_min N2Nat.inj_sub N2Nat.inj_double
     N2Nat.inj_succ N2Nat.inj_succ_double using solver : push_n2nat.
Hint Rewrite Nat2N.id N2Nat.id Nat2N.inj Nat2N.inj_add Nat2N.inj_mul
     Nat2N.inj_max Nat2N.inj_min Nat2N.inj_sub Nat2N.inj_double
     Nat2N.inj_succ Nat2N.inj_succ_double using solver : push_nat2n.
Hint Rewrite <- N2Nat.inj_add N2Nat.inj_mul
     N2Nat.inj_max N2Nat.inj_min N2Nat.inj_sub N2Nat.inj_double
     N2Nat.inj_succ N2Nat.inj_succ_double using solver : pull_n2nat.
Hint Rewrite <- Nat2N.inj_add Nat2N.inj_mul
     Nat2N.inj_max Nat2N.inj_min Nat2N.inj_sub Nat2N.inj_double
     Nat2N.inj_succ Nat2N.inj_succ_double using solver : pull_nat2n.

(* autorewrite database [nsimplify] for simplifying arithmetic in N *)
Hint Rewrite N.add_0_r N.add_0_l N.mul_0_r N.mul_0_l N.sub_0_r N.sub_0_l
     N.min_0_r N.min_0_l N.max_0_l N.max_0_r N.pow_0_l N.pow_0_r N.shiftr_0_l
     N.shiftr_0_r N.shiftl_0_l N.shiftl_0_r N.land_0_l N.land_0_r N.lor_0_l
     N.lor_0_r N.div_0_l N.mul_1_l N.mul_1_r N.log2_pow2 N.mod_0_l N.mod_1_r
     N.add_sub using solver : nsimplify.
Hint Rewrite N.mod_small N.mod_same N.mod_mod N.mod_mul N.mod_add using solver
  : nsimplify.
Hint Rewrite N.div_small N.div_same N.div_add N.div_add_l N.div_mul using solver
  : nsimplify.

(* autorewrite database [pull_nmod] for pulling N.modulo to the outside of
   expressions *)
Hint Rewrite <- N.mul_mod N.add_mod using solver : pull_nmod.
Hint Rewrite N.add_mod_idemp_l N.add_mod_idemp_r N.mul_mod_idemp_l
     N.mul_mod_idemp_r using solver : pull_nmod.

(* autorewrite database [push_nmul] for pushing N.mul to the inside of
   expressions *)
Hint Rewrite N.mul_add_distr_l N.mul_add_distr_r N.mul_sub_distr_l
     N.mul_sub_distr_r using solver : push_nmul.

(* Hint database bits2arith for converting bitshift operations to their
   arithmetic forms *)
Hint Rewrite N.shiftl_1_l N.shiftl_mul_pow2 N.shiftr_div_pow2 N.land_ones
     using solver : bits2arith.

(* Add common side conditions for N lemmas to [auto] *)
Hint Resolve N.pow_nonzero N.div_le_mono N.mod_bound_pos N.neq_0_lt_0 N.le_0_l
     N.lt_le_incl.

Ltac nsimplify := autorewrite with nsimplify.
Ltac nsimplify_all := autorewrite with nsimplify in *.
Ltac push_nat2n := autorewrite with push_nat2n;
                   try change (N.of_nat 0) with 0; cbn [N.succ BinPos.Pos.succ].
Ltac push_nat2n_all := autorewrite with push_nat2n in *;
                   try change (N.of_nat 0) with 0 in *; cbn [N.succ BinPos.Pos.succ] in *.
Ltac push_n2nat := autorewrite with push_n2nat.
Ltac push_n2nat_all := autorewrite with push_n2nat in *.

(* We have to handle N.add_mod and N.mul_mod carefully to keep from getting stuck
   in a loop like:
      (a + b) mod n
      (a mod n + b mod n) mod n
      ((a mod n) mod n + (b mod n) mod n) mod n
 *)
Ltac push_nmod_add n :=
  progress match goal with
           | |- context [(?a mod n + ?b mod n) mod n] => idtac
           | |- context [(?a + ?b) mod n] => rewrite (N.add_mod a b n) by solver
           end.
Ltac push_nmod_mul n :=
  progress match goal with
           | |- context [(?a mod n * (?b mod n)) mod n] => idtac
           | |- context [(?a * ?b) mod n] => rewrite (N.mul_mod a b n) by solver
           end.
Ltac push_nmod :=
  repeat match goal with
         | |- context [_ mod ?b] => push_nmod_add b
         | |- context [_ mod ?b] => push_nmod_mul b
         end.
Ltac pull_nmod := autorewrite with pull_nmod.
Ltac nsimplify_mod := push_nmod; nsimplify; pull_nmod.

(* tactics to automatically assert the property that (0 <= x mod y < y) for all
   expressions [x mod y] that are found somewhere in the proof state, and for
   which it can be proven that y <> 0 *)
Ltac assert_nmod_bounds' x y :=
  progress
    match goal with
    | H : (0 <= x mod y < y) |- _ => idtac
    | _ =>
      pose proof (N.mod_bound_pos x y ltac:(auto) ltac:(solver))
    end.
Ltac assert_nmod_bounds :=
  repeat match goal with
         | |- context [?x mod ?y] =>
           assert_nmod_bounds' x y
         | H : context [?x mod ?y] |- _ =>
           assert_nmod_bounds' x y
         end.

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
  Proof.
    rewrite <-N.compare_lt_iff, <-Nat.compare_lt_iff.
    rewrite N2Nat.inj_compare. reflexivity.
  Qed.

  (* this lemma exists to be added to [auto], so [auto] can solve [2 ^ _ <> 0] by
     [N.pow_nonneg] *)
  Lemma two_nonzero : 2 <> 0. Proof. congruence. Qed.
  Hint Resolve two_nonzero.

  Lemma div_mul_l a b : b <> 0 -> b * a / b = a.
  Proof. intros; rewrite N.mul_comm; nsimplify. solver. Qed.

  Lemma div_add_l' a b c :
    b <> 0 -> (b * a + c) / b = a + c / b.
  Proof. intros. rewrite (N.mul_comm b a). apply N.div_add_l; auto. Qed.
  Hint Rewrite div_add_l' using solver : nsimplify.

  Lemma div_add_l_exact a b :
    b <> 0 -> (b + a) / b = 1 + a / b.
  Proof.
    intros. replace (b + a) with (1 * b + a) by lia. nsimplify. reflexivity.
  Qed.

  Lemma mod_div_small a b :
    b <> 0 -> (a mod b / b) = 0.
  Proof.
    intros; apply N.div_small.
    apply N.mod_bound_pos; try apply N.neq_0_lt_0; auto.
  Qed.
  Hint Rewrite mod_div_small using solver : nsimplify.

  Lemma mul_div a b : b <> 0 -> b * (a / b) = a - a mod b.
  Proof.
    intros. rewrite (N.div_mod a b) by auto.
    repeat match goal with
           | _ => progress nsimplify
           | _ => progress nsimplify_mod
           | _ => solver
           end.
  Qed.

  Lemma mul_div' a b : b <> 0 -> (a / b) * b = a - a mod b.
  Proof. intros; rewrite N.mul_comm; apply mul_div; auto. Qed.

  Definition is_power_of_two (n : N) : Prop := n = N.pow 2 (N.log2 n).

  Lemma power_two_pos (n : N) :
    is_power_of_two n -> 0 < n.
  Proof.
    cbv [is_power_of_two]; intro H; rewrite H.
    apply N.lt_le_trans with (m:=2 ^ 0);
      [ rewrite N.pow_0_r; solver | ].
    apply N.pow_le_mono_r; solver.
  Qed.

  Lemma power_two_nonzero (n : N) :
    is_power_of_two n -> n <> 0.
  Proof.
    intros; pose proof power_two_pos n ltac:(assumption); solver.
  Qed.

  Lemma shiftl_power_two n :
    is_power_of_two (N.shiftl 1 n).
  Proof.
    cbv [is_power_of_two].
    autorewrite with bits2arith nsimplify.
    reflexivity.
  Qed.

  Lemma pow2_log2 (n : N) :
    is_power_of_two n -> 2 ^ N.log2 n = n.
  Proof.
    cbv [is_power_of_two]; intro H; rewrite H.
    autorewrite with bits2arith nsimplify.
    reflexivity.
  Qed.

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

  Lemma and_not a b :
    is_power_of_two b ->
    N.land a (N.lnot (b - 1) (N.size a)) = a - a mod b.
  Proof.
    intros; destruct (N.eq_dec a 0); [subst; nsimplify; reflexivity|].
    rewrite power_two_minus_1 by auto.
    rewrite <-N.ldiff_land_low by (rewrite N.size_log2; solver).
    rewrite N.ldiff_ones_r. autorewrite with bits2arith.
    rewrite mul_div', pow2_log2 by auto.
    reflexivity.
  Qed.

  Lemma power_two_trivial n :
    is_power_of_two (2 ^ n).
  Proof.
    cbv [is_power_of_two]. nsimplify; solver.
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
           | _ => progress nsimplify
           | _ => progress nsimplify_mod
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
           | _ => progress autorewrite with bits2arith
           | _ => solver
           end.
  Qed.

  Lemma shiftr_lt_shiftl_mono a b n :
    a < (N.shiftl b n) -> N.shiftr a n < b.
  Proof.
    repeat match goal with
           | _ => progress basics
           | _ => progress autorewrite with bits2arith in *
           | _ => apply N.div_lt_upper_bound
           | _ => solver
           end.
  Qed.

  Lemma shiftl_inj_iff a b n :
    a = b <-> N.shiftl a n = N.shiftl b n.
  Proof.
    autorewrite with bits2arith.
    rewrite N.mul_cancel_r by solver.
    reflexivity.
  Qed.

  Lemma mod_sub_small a b c :
    c <> 0 ->
    0 < a ->
    0 < b <= c ->
    (a * c - b) mod c = c - b.
  Proof.
    intros. assert (b <= a * c) by nia.
    transitivity ((a * c - b + c) mod c); [ nsimplify_mod; reflexivity | ].
    rewrite <-N.add_sub_swap by solver.
    rewrite <-N.add_sub_assoc by solver.
    nsimplify_mod. reflexivity.
  Qed.

  Lemma div_sub_small a b c :
    c <> 0 ->
    (0 < b <= c) ->
    (a * c - b) / c = a - 1.
  Proof.
    intros. destruct (N.eq_dec a 0); [ subst; solver | ].
    apply N.mul_cancel_l with (p:=c); [solver | ].
    rewrite mul_div, mod_sub_small by solver.
    autorewrite with push_nmul nsimplify. solver.
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
    induction b;
      repeat match goal with
             | _ => progress nsimplify
             | _ => progress push_nat2n
             | _ => rewrite N.pow_succ_r by solver
             | _ => rewrite Nat.pow_succ_r by solver
             | _ => solver
             end.
  Qed.
  Lemma zero_eq : N.of_nat 0 = 0.
  Proof. reflexivity. Qed.
  Lemma two_eq : N.of_nat 2 = 2.
  Proof. reflexivity. Qed.
End Nat2N.

Module N2Nat.
  Lemma zero_eq : N.to_nat 0 = 0%nat.
  Proof. reflexivity. Qed.
  Lemma two_eq : N.to_nat 2 = 2%nat.
  Proof. reflexivity. Qed.
End N2Nat.

(* add the lemmas defined here to the databases *)
Hint Rewrite Nat2N.inj_pow Nat2N.zero_eq Nat2N.two_eq using solver : push_nat2n.
Hint Rewrite <- Nat2N.inj_pow Nat2N.zero_eq Nat2N.two_eq using solver : pull_nat2n.
Hint Rewrite N2Nat.zero_eq N2Nat.two_eq using solver : push_n2nat.
Hint Rewrite <- N2Nat.zero_eq N2Nat.two_eq using solver : pull_n2nat.

Hint Rewrite N.pow2_log2 N.div_add_l' N.div_add_l_exact N.mod_div_small
     N.div_mul_l using solver : nsimplify.

Hint Rewrite N.land_ones' N.and_not using solver : bits2arith.
Hint Rewrite <-N.power_two_minus_1 using solver : bits2arith.

Hint Resolve N.power_two_trivial N.shiftl_power_two N.power_two_nonzero
     N.power_two_pos N.two_nonzero.
