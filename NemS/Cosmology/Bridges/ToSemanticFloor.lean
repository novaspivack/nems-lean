import NemS.Cosmology.UnifiedClosureFramework
import NemS.Cosmology.CosmologicalClosureSchema
import NemS.Cosmology.SemanticFloor
import NemS.MFRR.DiagonalBarrier
import NemS.Adjudication.ExecutionNecessity

/-!
# NemS.Cosmology.Bridges.ToSemanticFloor

**Bridge: Unified schema ⇒ Admissible initiality (semantic floor).**

Projects U through toCosmologicalFramework and invokes Paper 24's semantic_floor.
-/

set_option autoImplicit false

namespace NemS
namespace Cosmology
namespace Bridges

open NemS.Cosmology
open NemS.Cosmology.CosmologicalFramework
open NemS.Adjudication
open NemS.MFRR

/-- **Closure-admissible initiality** on the unified base.

The initial state satisfies the semantic floor: it can host diagonal capability
and internal adjudication without external selection. -/
def ClosureAdmissibleInitiality (U : UnifiedClosureFramework) : Prop :=
  (U.toCosmologicalFramework).SatisfiesSemanticFloor

/-- **Theorem: Closure schema ⇒ Admissible initiality.**

Under the cosmological closure schema, the initial state satisfies the semantic floor.
Proof: push U through toCosmologicalFramework, then invoke semantic_floor (Paper 24).
-/
theorem closure_schema_implies_admissible_initiality
    {U : UnifiedClosureFramework}
    (h : CosmologicalClosureSchema U) :
    ClosureAdmissibleInitiality U := by
  let F := U.toCosmologicalFramework
  have dc : DiagonalCapable F.toFramework := h.diagonal
  obtain ⟨U'⟩ := h.has_universe
  exact semantic_floor F U'

end Bridges
end Cosmology
end NemS
