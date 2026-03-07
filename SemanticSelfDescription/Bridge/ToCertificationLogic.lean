import CertificationLogic.Theorems.Maximality
import SemanticSelfDescription.Core.Claims
import SemanticSelfDescription.Theorems.NoFinalSelfTheory
import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import SelectorStrength.Instances.Trivial

/-!
# SemanticSelfDescription.Bridge.ToCertificationLogic

**Bridge: Necessary Incompleteness implies certification boundary (Paper 50).**

When a SelfSemanticFrame satisfies BarrierHypotheses and CodeEquiv coincides
with equality, the certification calculus boundary (CertificationLogic, Paper 50)
holds: no extension can yield a total decider.
-/

set_option autoImplicit false

namespace SemanticSelfDescription

universe u v

variable {W : Type u} (F : SelfSemanticFrame W)

/--
**Certification boundary under barrier hypotheses (equality case).**

When the frame satisfies BarrierHypotheses and CodeEquiv is equality, the
CertificationLogic boundary_maximality (Paper 50) applies: no total decider
exists for self-semantic truth.
-/
theorem certification_boundary_under_barrier
    (hB : BarrierHypotheses F)
    (hEquiv : ∀ a b : F.Code, hB.codeExt.CodeEquiv a b ↔ a = b) :
    ¬ SelectorStrength.DecidableAt SelectorStrength.S_all F.selfSemanticTruth := by
  have hExt : SelectorStrength.Extensional (· = ·) F.selfSemanticTruth :=
    fun {a} {b} hab => selfSemanticTruth_extensional F hB.codeExt ((hEquiv a b).mpr hab)
  have hFP : ∀ F' : F.Code → F.Code, SelectorStrength.S_all_α F' → ∃ d : F.Code, d = F' d :=
    fun F' _ => let ⟨d, hd⟩ := hB.hFP F'; ⟨d, (hEquiv d (F' d)).mp hd⟩
  exact CertificationLogic.boundary_maximality F.Code F.selfSemanticTruth
    hExt (@encodedNontrivial_implies_nontrivial W F hB.encoded)
    SelectorStrength.S_all SelectorStrength.S_all_α
    (SelectorStrength.antiDeciderClosed_all (α := F.Code))
    hFP

end SemanticSelfDescription
