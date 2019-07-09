Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Hafnium.AbstractModel.
Require Import Hafnium.Concrete.State.
Require Import Hafnium.Concrete.Datatypes.
Require Import Hafnium.Util.Tactics.
Require Import Hafnium.Concrete.Assumptions.Addr.
Require Import Hafnium.Concrete.Assumptions.Mpool.
Require Import Hafnium.Concrete.MM.Datatypes.
Require Import Hafnium.Concrete.MM.Implementation.

(*** This file contains correctness proofs for the functions in mm.c, as
     transcribed in MM/Implementation.v ***)

Section Proofs.
  Context {ap : @abstract_state_parameters paddr_t nat}
          {cp : concrete_params}.

  Local Definition preserves_represents
        (f : concrete_state -> concrete_state) : Prop :=
    forall (conc : concrete_state),
      (exists abst, represents abst conc) ->
      exists abst', represents abst' (f conc).
  Hint Unfold preserves_represents.

  Lemma mm_free_page_pte_represents
        (conc : concrete_state)
        pte level ppool :
    preserves_represents
      (fun conc => fst (mm_free_page_pte conc pte level ppool)).
  Admitted.

  Lemma mm_replace_entry_represents
        (conc : concrete_state)
        begin t pte_index new_pte level flags ppool :
    preserves_represents
      (fun conc =>
         snd (fst (mm_replace_entry
                     conc begin t pte_index new_pte level flags ppool))).
  Admitted.

  Lemma mm_populate_table_pte_represents
        (conc : concrete_state)
        begin t pte_index level flags ppool :
    preserves_represents
      (fun conc =>
         snd (fst (mm_populate_table_pte
                     conc begin t pte_index level flags ppool))).
  Admitted.

  Lemma mm_map_level_represents
        (conc : concrete_state)
        t begin end_ attrs table level flags ppool :
    preserves_represents
      (fun conc =>
         snd (fst (mm_map_level
                     conc t begin end_ attrs table level flags ppool))).
  Admitted.

  Lemma mm_map_root_represents
        (conc : concrete_state)
        t begin end_ attrs root_level flags ppool :
    preserves_represents
      (fun conc =>
         snd (fst (mm_map_root
                     conc t begin end_ attrs root_level flags ppool))).
  Admitted.

  Lemma mm_ptable_identity_update_represents
        (conc : concrete_state)
        t pa_begin pa_end attrs flags ppool :
    preserves_represents
      (fun conc =>
         snd (fst (mm_ptable_identity_update
                     conc t pa_begin pa_end attrs flags ppool))).
  Admitted.

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
