import Closure.Core.ObsSemantics
import Closure.Theorems.Preservation
import HolographyUnderClosure.Core.Semantics

/-!
# HolographyUnderClosure.Core.Interpretation

**Paper 48: Closure-preserving interpretation (holographic map).**

Uses Closure's Interpretation: worldMap (boundary → bulk), obsMap (bulk obs → boundary obs),
satisfaction preservation. **SurjWT** = surjective on world-types: every bulk world-type
is the image of some boundary world under worldMap (boundary "encodes" bulk).
-/

set_option autoImplicit false

namespace HolographyUnderClosure

universe u v

variable {World₁ World₂ : Type u} {Obs₁ Obs₂ : Type v}
  (S₁ : Closure.ObsSemantics World₁ Obs₁) (S₂ : Closure.ObsSemantics World₂ Obs₂)

/-- **Holographic interpretation**: boundary semantics interprets into bulk.
Closure.Theorems.Preservation.Interpretation with worldMap : boundary → bulk. -/
def HolographicInterpretation :=
  Closure.Interpretation World₁ Obs₁ S₁ World₂ Obs₂ S₂

/-- **Surjective on world-types (SurjWT):** every bulk world-type has a boundary representative. -/
def SurjWT (I : Closure.Interpretation World₁ Obs₁ S₁ World₂ Obs₂ S₂) : Prop :=
  I.surjectiveOnWorldTypes

end HolographyUnderClosure
