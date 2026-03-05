import HolographyUnderClosure.Core.WorldTypeMaps

/-!
# HolographyUnderClosure.Theorems.WorldTypeHolography

**Paper 48 T48.1: World-type holography (surjective encoding).**

If the interpretation is surjective on world-types (SurjWT), then every bulk
world-type has a boundary representative; bulk observational invariants factor
through boundary. This is the minimal "holographic duality" claim.
-/

set_option autoImplicit false

namespace HolographyUnderClosure

universe u v

variable {World₁ World₂ : Type u} {Obs₁ Obs₂ : Type v}
  (S₁ : Closure.ObsSemantics World₁ Obs₁) (S₂ : Closure.ObsSemantics World₂ Obs₂)
  (I : Closure.Interpretation World₁ Obs₁ S₁ World₂ Obs₂ S₂)

/-- **T48.1 Surjective world-type encoding.** If SurjWT holds, then the induced
WTMap is surjective: every bulk world-type is the image of some boundary world-type. -/
theorem surj_worldtype_encoding (hSurj : I.surjectiveOnWorldTypes) :
    Function.Surjective (WTMap S₁ S₂ I) :=
  (surjective_WTMap_iff S₁ S₂ I).mpr hSurj

end HolographyUnderClosure
