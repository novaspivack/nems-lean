import NemS.Cosmology.UnifiedClosureFramework
import NemS.Cosmology.SemanticFloor
import NemS.MFRR.PSCBundle
import NemS.MFRR.DiagonalBarrier
import NemS.Adjudication.ExecutionNecessity

/-!
# NemS.Cosmology.CosmologicalClosureSchema

**Grand schema on the unified base (Paper 78).**

The closure schema as a predicate on UnifiedClosureFramework. Includes only
assumptions that feed the three theorem stacks. No conclusion-shaped predicates.
-/

set_option autoImplicit false

namespace NemS
namespace Cosmology

open NemS.MFRR
open NemS.Adjudication

/-- Trivial internality predicate for schema: every selector counts as internal. -/
def trivialInternal (U : UnifiedClosureFramework) : U.toFramework.Selector → Prop :=
  fun _ => True

/-- **Cosmological Closure Schema.**

Bundles the assumptions needed for all three bridge theorems:
- diagonal + universe → admissible initiality (Semantic Floor)
- (RecordFiltration is always present) → structural irreversibility
- psc → no external selection (no_external_law)
-/
structure CosmologicalClosureSchema (U : UnifiedClosureFramework) where
  /-- The framework is diagonal-capable (ASR). -/
  diagonal : DiagonalCapable U.toFramework
  /-- The framework supports a universe (internal adjudication). -/
  has_universe : Nonempty (Universe U.toFramework)
  /-- PSC holds (no external model selection). -/
  psc : PSCBundle U.toFramework (trivialInternal U)

end Cosmology
end NemS
