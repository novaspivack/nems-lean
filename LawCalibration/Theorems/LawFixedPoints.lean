import LawCalibration.Core.LawUpdate

/-!
# LawCalibration.Theorems.LawFixedPoints

**Paper 44: Existence and multiplicity of law fixed points.**

Every law is a fixed point of the update (for the minimal model U = id).
Multiplicity: there exist at least two distinct fixed points (minimal and other).
-/

set_option autoImplicit false

namespace LawCalibration

open Law

/-- **Every element is a fixed point** when U = id. -/
theorem all_fixed (ℓ : Law) : IsFixedPoint ℓ :=
  rfl

/-- **Fixed-point existence**: at least one fixed point. -/
theorem fixed_point_exists : ∃ ℓ : Law, IsFixedPoint ℓ :=
  ⟨Law.minimal, all_fixed Law.minimal⟩

/-- **Multiplicity**: at least two distinct fixed points. -/
theorem fixed_point_multiplicity : ∃ ℓ₁ ℓ₂ : Law, IsFixedPoint ℓ₁ ∧ IsFixedPoint ℓ₂ ∧ ℓ₁ ≠ ℓ₂ :=
  ⟨Law.minimal, Law.other, all_fixed Law.minimal, all_fixed Law.other, Law.noConfusion⟩

/-- **Minimal fixed point exists**. -/
theorem minimal_fixed_point : IsFixedPoint Law.minimal ∧ IsMinimalFixedPoint Law.minimal :=
  ⟨all_fixed Law.minimal, rfl⟩

end LawCalibration
