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

  (* TODO: move *)
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
End N.
