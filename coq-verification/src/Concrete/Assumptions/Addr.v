Require Import Hafnium.Concrete.Datatypes.

(*** This file defines (the necessary parts of) the API provided by addr.h,
     which is assumed correct for now. In order to replace this assumption with
     a proof of correctness, replace the [Axiom]s with definitions and proofs,
     leaving their types the same. ***)

Axiom ipaddr_t : Type.

Axiom paddr_t : Type.

Axiom pa_addr : paddr_t -> uintpaddr_t.

Axiom ipa_addr : ipaddr_t -> uintpaddr_t.

Axiom ipa_add : ipaddr_t -> size_t -> ipaddr_t.

Axiom pa_from_ipa : ipaddr_t -> paddr_t.

(* TODO: add axioms for correctness properties, as needed *)
