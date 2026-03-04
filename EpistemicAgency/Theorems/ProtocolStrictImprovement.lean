import NemS.Prelude
import EpistemicAgency.Core.ClaimDomain
import EpistemicAgency.Core.Protocol

/-!
# EpistemicAgency.Theorems.ProtocolStrictImprovement

**Strict separation: society can certify strictly more than any individual (Paper 31).**

Coverage of the union protocol equals the union of individual covers.
Each individual cover is contained in the society cover; when the union is strictly
larger than an individual's cover, we have strict improvement.
-/

set_option autoImplicit false

namespace EpistemicAgency

variable {D : ClaimDomain}

open ClaimDomain

/-- Each individual cover is contained in the society cover. -/
theorem individual_cover_subset_society (soc : Society D) (_h : SocietySound soc)
    (p : Verifier D × Finset D.ClaimId) (hp : p ∈ soc) :
    p.2 ⊆ societyCover soc := by
  intro c hc
  rw [mem_societyCover_iff]
  exact ⟨p, hp, hc⟩

/-- **Strict improvement**: if the society cover has an element outside a given
member's cover, then that member's cover is contained in the society cover and
the society cover has an element not in that member's cover (strict improvement). -/
theorem protocol_strict_improvement (soc : Society D) (h : SocietySound soc)
    (p : Verifier D × Finset D.ClaimId) (hp : p ∈ soc)
    (c : D.ClaimId) (hc : c ∈ societyCover soc) (hc' : c ∉ p.2) :
    p.2 ⊆ societyCover soc ∧ ∃ d ∈ societyCover soc, d ∉ p.2 :=
  ⟨individual_cover_subset_society soc h p hp, ⟨c, hc, hc'⟩⟩

end EpistemicAgency
