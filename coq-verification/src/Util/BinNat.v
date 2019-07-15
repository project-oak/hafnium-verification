Require Import Coq.Arith.PeanoNat.
Require Import Coq.NArith.BinNat.
Require Import Coq.NArith.Nnat.
Local Open Scope N_scope.

Module N.
  Lemma to_nat_ltb (x y : N) :
    (x <? y)%N = (N.to_nat x <? N.to_nat y)%nat.
  Proof.
    rewrite N.ltb_compare, Nat.ltb_compare.
    rewrite N2Nat.inj_compare.
    reflexivity.
  Qed.
End N.
