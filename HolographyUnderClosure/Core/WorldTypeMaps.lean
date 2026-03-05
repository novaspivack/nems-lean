import Closure.Core.ObsSemantics
import Closure.Theorems.Preservation
import HolographyUnderClosure.Core.Interpretation

/-!
# HolographyUnderClosure.Core.WorldTypeMaps

**Paper 48: Induced map from boundary world-types to bulk world-types.**

Under an interpretation, ObsEquiv is preserved (Preservation.obsEquiv_preserved),
so we get a well-defined map **WTMap** : S₂.WorldType → S₁.WorldType. Surjectivity
of this map is exactly SurjWT (surjectiveOnWorldTypes).
-/

set_option autoImplicit false

namespace HolographyUnderClosure

universe u v

variable {World₁ World₂ : Type u} {Obs₁ Obs₂ : Type v}
  (S₁ : Closure.ObsSemantics World₁ Obs₁) (S₂ : Closure.ObsSemantics World₂ Obs₂)
  (I : Closure.Interpretation World₁ Obs₁ S₁ World₂ Obs₂ S₂)

open Closure

/-- **Induced world-type map:** boundary world-type → bulk world-type.
Well-defined because interpretation preserves ObsEquiv. -/
def WTMap : S₂.WorldType → S₁.WorldType :=
  Quotient.lift (fun w₂ => S₁.toWorldType (I.worldMap w₂)) fun w₂₁ w₂₂ h => by
    have hobs : S₂.ObsEquiv w₂₁ w₂₂ := h
    exact (S₁.toWorldType_eq_iff (I.worldMap w₂₁) (I.worldMap w₂₂)).mpr
      (@Closure.Interpretation.obsEquiv_preserved World₁ World₂ Obs₁ Obs₂ S₁ S₂ I w₂₁ w₂₂ hobs)

/-- **WTMap is surjective** iff every bulk world-type has a boundary representative. -/
theorem surjective_WTMap_iff : Function.Surjective (WTMap S₁ S₂ I) ↔ I.surjectiveOnWorldTypes := by
  constructor
  · intro h t₁
    obtain ⟨t₂, heq⟩ := h t₁
    induction t₂ using Quotient.inductionOn with
    | _ w₂ => exact ⟨w₂, heq⟩
  · intro h t₁
    obtain ⟨w₂, heq⟩ := h t₁
    exact ⟨Quotient.mk S₂.obsEquivSetoid w₂, heq⟩

end HolographyUnderClosure
