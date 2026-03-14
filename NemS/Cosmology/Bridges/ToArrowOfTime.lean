import NemS.Cosmology.UnifiedClosureFramework
import NemS.Cosmology.CosmologicalClosureSchema
import ArrowOfTime.Theorems.Irreversibility

/-!
# NemS.Cosmology.Bridges.ToArrowOfTime

**Bridge: Unified schema ⇒ Structural irreversibility.**

Interprets StructuralIrreversibility as the no-global-reversal fact inherited
from Paper 36 (ArrowOfTime). A stage-preserving involution cannot undo refinement.
-/

set_option autoImplicit false

namespace NemS
namespace Cosmology
namespace Bridges

open NemS.Cosmology
open ArrowOfTime

/-- **Structural irreversibility** on the unified base.

Defined as the no-global-reversal fact from Paper 36: any stage-preserving
involution fixes every stage world-type; it cannot distinguish fewer worlds.
This holds for any RecordFiltration — no extra schema assumptions required. -/
def StructuralIrreversibility (U : UnifiedClosureFramework) : Prop :=
  ∀ (R : U.World → U.World),
    ArrowOfTime.IsInvolution R →
    ArrowOfTime.StagePreserving (U.toRecordFiltration) R →
    ∀ t w, (U.toRecordFiltration).toWorldTypeAt t (R w) = (U.toRecordFiltration).toWorldTypeAt t w

/-- **Theorem: Closure schema ⇒ Structural irreversibility.**

Under the cosmological closure schema, structural irreversibility holds.
Proof: no_global_reversal (Paper 36) holds for any RecordFiltration. -/
theorem closure_schema_implies_structural_irreversibility
    {U : UnifiedClosureFramework}
    (_h : CosmologicalClosureSchema U) :
    StructuralIrreversibility U := by
  intro R _hInv hStage t w
  exact ArrowOfTime.no_global_reversal (U.toRecordFiltration) R _hInv hStage t w

end Bridges
end Cosmology
end NemS
