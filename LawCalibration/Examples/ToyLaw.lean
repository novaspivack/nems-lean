import LawCalibration.Core.LawUpdate
import LawCalibration.Theorems.LawFixedPoints
import LawCalibration.Theorems.LawSelectionBarrier

/-!
# LawCalibration.Examples.ToyLaw

**Paper 44: Toy law instance — multiplicity and concept only.**

The toy uses the core Law (minimal | other) and lawUpdate = id. It witnesses **multiplicity**
(two distinct fixed points) and the **concept** of minimal fixed points (lawSelectorClaim is
nontrivial in the single-instance sense). The **barrier** is not claimed for the toy predicate
(that would be trivially decidable); the barrier applies to the uniform predicate over
LawInstanceCode (no_total_decider_uniform_law_selector).
-/

set_option autoImplicit false

namespace LawCalibration

/-- **Toy: multiplicity** — two distinct fixed points (re-export from LawFixedPoints). -/
theorem toy_fixed_point_multiplicity :
    ∃ ℓ₁ ℓ₂ : Law, IsFixedPoint ℓ₁ ∧ IsFixedPoint ℓ₂ ∧ ℓ₁ ≠ ℓ₂ :=
  fixed_point_multiplicity

/-- **Toy: single-instance claim is nontrivial** (concept only; barrier is on uniform predicate). -/
theorem toy_lawSelectorClaim_nontrivial : SelectorStrength.Nontrivial lawSelectorClaim :=
  lawSelectorClaim_nontrivial

/-- **Uniform barrier** applies: no total decider for uniform law-selector claim (re-export for paper). -/
theorem toy_no_total_decider_uniform_law_selector
    (Sbool : SelectorStrength.Strength LawInstanceCode Bool)
    (Sα : SelectorStrength.Strength LawInstanceCode LawInstanceCode)
    (hAnti : SelectorStrength.AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : LawInstanceCode → LawInstanceCode, Sα F → ∃ d : LawInstanceCode, d = F d) :
    ¬ SelectorStrength.DecidableAt Sbool uniformLawSelectorClaim :=
  no_total_decider_uniform_law_selector Sbool Sα hAnti hFP

end LawCalibration
