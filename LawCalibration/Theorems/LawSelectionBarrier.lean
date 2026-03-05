import LawCalibration.Core.LawUpdate
import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import SelectorStrength.Theorems.BarrierSchema

/-!
# LawCalibration.Theorems.LawSelectionBarrier

**Paper 44: No total-effective uniform law selector under diagonal capability.**

The **uniform** law-selector claim (candidate is a minimal fixed point for the encoded instance ↔ claimed)
is extensional and nontrivial on LawInstanceCode. Under AntiDeciderClosed and hFP instantiated on the
code domain, no total-effective decider exists for that uniform predicate (SelectorStrength schema).

The toy single-instance predicate (lawSelectorClaim on LawCode) is not the barrier target—it is
trivially decidable; the barrier applies to selection across encoded law-update instances.
-/

set_option autoImplicit false

namespace LawCalibration

/-- **Toy** law-selector claim is extensional (for concept; barrier is not on this). -/
theorem lawSelectorClaim_extensional :
    SelectorStrength.Extensional (· = ·) lawSelectorClaim := by
  intro x y heq
  rw [heq]

/-- **Toy** law-selector claim is nontrivial (for concept; barrier is not on this). -/
theorem lawSelectorClaim_nontrivial : SelectorStrength.Nontrivial lawSelectorClaim := by
  refine ⟨⟨⟨Law.minimal, true⟩, by simp [lawSelectorClaim, IsMinimalFixedPoint]⟩,
    ⟨⟨Law.minimal, false⟩, by simp [lawSelectorClaim, IsMinimalFixedPoint]⟩⟩

/-- **Uniform** law-selector claim is extensional for equality on LawInstanceCode. -/
theorem uniformLawSelectorClaim_extensional :
    SelectorStrength.Extensional (· = ·) uniformLawSelectorClaim := by
  intro x y heq
  rw [heq]

/-- **Uniform** law-selector claim is nontrivial: (inst0, minimal, true) holds; (inst0, minimal, false) does not. -/
theorem uniformLawSelectorClaim_nontrivial : SelectorStrength.Nontrivial uniformLawSelectorClaim := by
  refine ⟨⟨⟨InstanceIndex.inst0, Law.minimal, true⟩, by simp [uniformLawSelectorClaim, isMinimalForInstance]⟩,
    ⟨⟨InstanceIndex.inst0, Law.minimal, false⟩, by simp [uniformLawSelectorClaim, isMinimalForInstance]⟩⟩

/-- **Law selection barrier (uniform):** Under AntiDeciderClosed and hFP at strength S on the *code* domain,
no total decider in Sbool exists for the uniform law-selector claim over encoded instances. -/
theorem no_total_decider_uniform_law_selector
    (Sbool : SelectorStrength.Strength LawInstanceCode Bool)
    (Sα : SelectorStrength.Strength LawInstanceCode LawInstanceCode)
    (hAnti : SelectorStrength.AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : LawInstanceCode → LawInstanceCode, Sα F → ∃ d : LawInstanceCode, d = F d) :
    ¬ SelectorStrength.DecidableAt Sbool uniformLawSelectorClaim :=
  SelectorStrength.no_total_decider_at_strength_nontrivial (· = ·) uniformLawSelectorClaim
    uniformLawSelectorClaim_extensional uniformLawSelectorClaim_nontrivial Sbool Sα hAnti hFP

end LawCalibration
