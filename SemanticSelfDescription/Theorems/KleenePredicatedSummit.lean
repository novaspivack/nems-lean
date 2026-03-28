import SemanticSelfDescription.Instances.KleenePartrec
import SemanticSelfDescription.Bridge.AugmentBarrierHypotheses

/-!
# SemanticSelfDescription.Theorems.KleenePredicatedSummit

**Summit status: predicated computational barrier (Kleene / `Nat.Partrec.Code`).**

This module packages the honest **achieved** target for the computational line:

* a concrete **`SelfSemanticFrame`** (**`kleenePartrecFrame`**);
* **extensional** code equivalence (**`kleeneCodeEquiv`**, neither raw equality nor a universal relation);
* **`EncodedNontrivial`** and a stable realized-truth predicate;
* a **real** Rogers / fixed-point package in the form **`BarrierHypothesesPred`** with
  **`P = kleeneComputableTransformerPred`** (**`Computable`** maps on code numbers).

**Boundary (not laziness):** unconditional **`BarrierHypotheses`** is **strictly stronger**: it asks
code fixed points for **every** `F' : Code → Code`. The Kleene instance is **mathematically correct**
only at the **class-restricted** layer. Upgrading to **`BarrierHypotheses`** is still
**`BarrierHypothesesPred.toBarrierHypotheses`**, and that needs a proof that **`P F'`** holds **for all**
transformers — which **fails** for **`P = Computable`** (not every `ℕ → ℕ` function is computable).

The **optional stronger route** (proof-theoretic middle equivalence, stronger representability, …) is a
**separate** ascent; it should not be smuggled by collapsing **`BarrierHypothesesPred`** into
**`BarrierHypotheses`** without that extra input.

See also **`SemanticSelfDescription.Theorems.SummitComparison`** (**strict separation** vs proof-theoretic
**`BarrierHypotheses`**: **`not_forall_kleeneComputableTransformerPred`**, **`kleenePredicated_toBarrierHypotheses_side_condition_false`**),
**`StructuralNonExhaustibility.Bridges.ToSemanticSelfDescription`** (**`reflexiveSystem_ofSelfSemanticFramePred`**),
and **`StructuredNonexhaustibility.KleenePredicatedResidualSummit`** (reflexive enriched **R₄** endpoint).
-/

set_option autoImplicit false

namespace SemanticSelfDescription

/--
**Theorem (predicated computational summit).**

**`F_Kleene`** carries **`BarrierHypothesesPred`** for the **computable** Rogers class.
-/
theorem kleene_computational_predicated_summit :
    Nonempty (BarrierHypothesesPred kleenePartrecFrame kleeneComputableTransformerPred) :=
  ⟨kleeneComputationalBarrierHypotheses⟩

/--
**Repr-augmented predicated hypotheses** from any global `(U₁)` proposition `Q` and witness `hQ`.

Typical use: `Q := (∀ ρ, ¬ A.repr_success ρ)` with `hQ := b.reprBarrier` from **`U123BarrierData`**.
-/
theorem kleene_reprAugmented_computational_barrier_nonempty (Q : Prop) (hQ : Q) :
    Nonempty
      (BarrierHypothesesPred kleenePartrecFrame kleeneComputableTransformerPred) :=
  ⟨barrierHypothesesPred_augment_withGlobalConjunct kleenePartrecFrame kleeneComputationalBarrierHypotheses Q hQ⟩

end SemanticSelfDescription
