import InstitutionalEpistemics.Core.Roles
import InstitutionalEpistemics.Theorems.RobustnessImprovement

/-! Paper 49, T49.2: Diversity necessary for strict improvement (re-export Paper 40). -/

set_option autoImplicit false

variable (Instance : Type*) [Fintype Instance] [DecidableEq Instance] (n : ℕ) [DecidableEq (Role n)]

namespace CosmicAudit

/-- **T49.2 (re-export):** Strict improvement ⇒ diversity (at least two non-equivalent roles).
    Cosmic interpretation: a distributed audit that strictly improves over any
    single context must have diverse roles (Paper 40). -/
theorem diversity_necessary_strict_improvement
    (cov : Role n → Finset Instance)
    (h : InstitutionalEpistemics.StrictImprovement Instance n cov)
    (hcard : n ≥ 2) :
    Diversity Instance n (fun r => (· ∈ cov r)) :=
  InstitutionalEpistemics.diversity_necessity Instance n cov h hcard

end CosmicAudit
