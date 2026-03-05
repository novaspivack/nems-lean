import InstitutionalEpistemics.Theorems.RobustnessImprovement
import InstitutionalEpistemics.Core.Roles

set_option autoImplicit false

/-!
# ErrorCorrectingClosure.Theorems.ProtocolImprovement

**Paper 43: Societies improve decoding coverage (wrapper over Paper 40).**

Decoding coverage is interpreted as protocol coverage: each role certifies (decodes)
a set of instances. When the protocol's decoding coverage strictly improves over
any single role, diversity is necessary (at least two roles with distinct coverage).
-/

namespace ErrorCorrectingClosure

open InstitutionalEpistemics

variable (Instance : Type*) [Fintype Instance] [DecidableEq Instance] (n : ℕ) [DecidableEq (Role n)]

/-- **Decoding coverage** of a protocol: union of coverage sets of roles.
(Re-export of InstitutionalEpistemics.protocolCoverage with decoding interpretation.) -/
def decodingCoverage (cov : Role n → Finset Instance) : Finset Instance :=
  protocolCoverage Instance n cov

/-- **Strict decoding improvement**: protocol decoding coverage is strictly larger
than that of any single role. -/
def StrictDecodingImprovement (cov : Role n → Finset Instance) : Prop :=
  StrictImprovement Instance n cov

/-- **Diversity necessity for decoding:** strict decoding improvement implies
at least two non-equivalent roles (diversity). -/
theorem diversity_necessity_decoding (cov : Role n → Finset Instance)
    (h : StrictDecodingImprovement Instance n cov) (hcard : n ≥ 2) :
    Diversity Instance n (fun r => (· ∈ cov r)) :=
  diversity_necessity Instance n cov h hcard

end ErrorCorrectingClosure
