import NemS.Prelude
import EpistemicAgency.Core.ClaimDomain
import EpistemicAgency.Core.Protocol
import EpistemicAgency.Theorems.ProtocolStrictImprovement
import EpistemicAgency.Theorems.Diversity

/-!
# SelfImprovement.Theorems.SocietyImproves

**Society improves improvement (Paper 32, T3–T4).**

Protocol strict improvement and diversity necessity applied to upgrade verification.
Upgrade-claim domain is a ClaimDomain (claim IDs = upgrade scenarios); theorems
from EpistemicAgency (Paper 31) apply verbatim.
-/

set_option autoImplicit false

namespace SelfImprovement

variable {D : EpistemicAgency.ClaimDomain}

open EpistemicAgency EpistemicAgency.ClaimDomain

/-- **Protocol strict improvement for upgrade verification (wrapper).**

In a finite upgrade-claim domain, role-separated auditors with complementary
coverage and an admissible protocol (e.g. union) yield certified coverage
strictly larger than any individual. This is Paper 31's protocol_strict_improvement. -/
theorem protocol_strict_improvement_upgrades (soc : Society D) (h : SocietySound soc)
    (p : Verifier D × Finset D.ClaimId) (hp : p ∈ soc)
    (c : D.ClaimId) (hc : c ∈ societyCover soc) (hc' : c ∉ p.2) :
    p.2 ⊆ societyCover soc ∧ ∃ d ∈ societyCover soc, d ∉ p.2 :=
  EpistemicAgency.protocol_strict_improvement soc h p hp c hc hc'

/-- **Diversity necessity for strict improvement (wrapper).**

If an admissible protocol strictly improves certified upgrade coverage, the society
must have role diversity (non-identical coverage sets). This is Paper 31's diversity_necessary. -/
theorem diversity_necessary_upgrades (soc : Society D) (hSound : SocietySound soc)
    (Prot : List (Verifier D) → Verifier D) (hAdm : Admissible Prot)
    (hStrict : ∃ c, Prot (societyVerifiers soc) c ≠ Verdict.abstain ∧ ∀ p ∈ soc, c ∉ p.2)
    (hnonempty : ∃ p, p ∈ soc) :
    ¬ ∃ C, Homogeneous soc C :=
  EpistemicAgency.diversity_necessary soc hSound Prot hAdm hStrict hnonempty

end SelfImprovement
