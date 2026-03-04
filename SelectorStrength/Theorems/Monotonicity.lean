import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders

/-!
# SelectorStrength.Theorems.Monotonicity

**Monotonicity: stronger strength ⇒ more decidable predicates (Paper 29).**

If S₁ ≤ S₂ then DecidableAt S₁ T → DecidableAt S₂ T.
-/

set_option autoImplicit false

namespace SelectorStrength

universe u

variable {α : Type u}

/-- If S₁ ≤ S₂ then every predicate decidable at S₁ is decidable at S₂. -/
theorem decidableAt_mono (T : α → Prop) (S₁ S₂ : Strength α Bool) (hle : S₁ ≤ S₂) :
    DecidableAt S₁ T → DecidableAt S₂ T := by
  intro ⟨δ, hS₁δ, hDec⟩
  exact ⟨δ, hle δ hS₁δ, hDec⟩

end SelectorStrength
