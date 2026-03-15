import SelectorStrength.Theorems.BarrierSchema
import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import Hypercomputation.Core.HypercomputerClaim
import Hypercomputation.Core.Taxonomy
import Hypercomputation.Theorems.NoInternalHypercomputer

/-!
# Hypercomputation.Theorems.Taxonomy

**Hypercomputation taxonomy theorem (Paper 35).**

A purported internal total hypercomputer claim forces failure of at least
one barrier premise: diagonal (anti-decider closure / fixed-point),
extensionality, nontriviality, or totality. This is the formal disjunctive
classification of escape routes.
-/

set_option autoImplicit false

namespace Hypercomputation

open SelectorStrength

universe u

variable {α : Type u}
variable (Equiv : α → α → Prop)
variable (Sbool : Strength α Bool) (Sα : Strength α α)

/-- **Internal hypercomputer claim forces premise failure (Paper 35 taxonomy).**

If someone claims an internal total hypercomputer for T (i.e. DecidableAt Sbool T),
then at least one of the barrier premises must fail: either anti-decider closure,
the fixed-point principle, extensionality, or nontriviality.

Proof: if all four held, the barrier would give ¬DecidableAt; contradiction. -/
theorem internal_hypercomputer_claim_forces_premise_failure (T : α → Prop)
    (hHC : HasInternalHypercomputerAt Sbool T) :
    FailsDiagonalPremise Equiv Sbool Sα ∨
    @FailsExtensionality α Equiv T ∨
    FailsNontriviality T := by
  by_contra hAll
  push_neg at hAll
  obtain ⟨hNotDiag, hNotExt, hNotNon⟩ := hAll
  have hAnti : AntiDeciderClosed Sbool Sα := by
    by_contra h
    exact hNotDiag (Or.inl h)
  have hFP : ∀ F : α → α, Sα F → ∃ d : α, Equiv d (F d) := by
    intro F hF
    by_contra h
    exact hNotDiag (Or.inr (fun h' => h (h' F hF)))
  have hExt : Extensional Equiv T := by
    by_contra h
    exact hNotExt h
  have hNon : Nontrivial T := by
    by_contra h
    exact hNotNon h
  exact no_internal_hypercomputer_at_strength Equiv Sbool Sα T hExt hNon hAnti hFP hHC

/-- **Hypercomputation taxonomy.** Alias. -/
theorem hypercomputation_taxonomy (T : α → Prop)
    (hHC : HasInternalHypercomputerAt Sbool T) :
    FailsDiagonalPremise Equiv Sbool Sα ∨
    @FailsExtensionality α Equiv T ∨
    FailsNontriviality T :=
  internal_hypercomputer_claim_forces_premise_failure Equiv Sbool Sα T hHC

end Hypercomputation
