import NemS.Cosmology.UnifiedClosureFramework
import NemS.Cosmology.CosmologicalClosureSchema
import NemS.MFRR.BridgeToNEMS

/-!
# NemS.Cosmology.Bridges.ToFinality

**Bridge: Unified schema ⇒ Internal realized history (no external selection).**

Defines ClosureRealizedHistory as ¬ NeedsExternalSelection and proves it
from PSC via no_external_law (NEMS/MFRR bridge).
-/

set_option autoImplicit false

namespace NemS
namespace Cosmology
namespace Bridges

open NemS.Cosmology
open NemS.Framework
open NemS.MFRR

/-- **Closure realized history** on the unified base.

The framework does not need external model selection. This is the NEMS/MFRR-flavored
formulation; the stronger Paper 23 finality trilemma is a separate corollary. -/
def ClosureRealizedHistory (U : UnifiedClosureFramework) : Prop :=
  ¬ NeedsExternalSelection U.toFramework (trivialInternal U)

/-- **Theorem: Closure schema ⇒ Internal realized history.**

Under the cosmological closure schema (which includes PSC), the framework
does not need external model selection. Proof: no_external_law. -/
theorem closure_schema_implies_internal_realized_history
    {U : UnifiedClosureFramework}
    (h : CosmologicalClosureSchema U) :
    ClosureRealizedHistory U :=
  NemS.MFRR.no_external_law h.psc

end Bridges
end Cosmology
end NemS
