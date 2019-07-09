Require Import Coq.Arith.PeanoNat.
Require Import Hafnium.AbstractModel.
Require Import Hafnium.Concrete.State.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Util.Tactics.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.Mpool.
Require Import Hafnium.Concrete.MM.Implementation.

(*** This file contains correctness proofs for the functions in mm.c, as
     transcribed in MM/Implementation.v ***)

Section Proofs.
  Context {ap : @abstract_state_parameters paddr_t nat}
          {cp : concrete_params}.

  Local Definition preserves_represents
        (f : concrete_state -> concrete_state) : Prop :=
    forall (ap : abstract_state_parameters) (cp : concrete_params)
           (conc : concrete_state),
      (exists abst, represents abst conc) ->
      exists abst', represents abst' (f conc).

  Lemma mm_identity_map_represents
        (conc : concrete_state)
        begin end_ mode ppool :
    preserves_represents
      (fun conc => snd (fst (mm_identity_map conc begin end_ mode ppool))).
  Admitted.

  Lemma mm_defrag_represents
        (conc : concrete_state)
        ppool :
    preserves_represents
      (fun conc => fst (mm_defrag conc ppool)).
  Admitted.

  Lemma mm_unmap_represents
        (conc : concrete_state)
        begin end_ ppool :
    preserves_represents
      (fun conc => snd (fst (mm_unmap conc begin end_ ppool))).
  Admitted.
End Proofs.
