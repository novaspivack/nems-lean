import NemS.Cosmology.UnifiedClosureFramework
import RecordEntropy.Core.HiddenHistoryEntropy
import ArrowOfTime.Theorems.ArrowRefinement

/-!
# NemS.Cosmology.Bridges.ToHiddenHistoryEntropy

**Bridge: Unified filtration ⇒ Fiber-based hidden-history entropy (fiber-based hidden entropy track).**

Wires the fiber-size refinement theorem to the unified closure framework.

**Two entropy directions (fiber-based hidden entropy track):**
- **Record resolution** (ToRecordResolution): card(WorldTypeAt t) INCREASES under refinement.
- **Fiber-based hidden multiplicity**: fiberSize(c) DECREASES under refinement — each t-class
  splits into smaller (t+1)-classes. When StrictGrowthAt t, the decrease is strict for
  some classes.
-/

set_option autoImplicit false

namespace NemS
namespace Cosmology
namespace Bridges

open NemS.Cosmology
open ArrowOfTime
open RecordEntropy

variable (U : UnifiedClosureFramework) (t : ArrowOfTime.Time)
variable [Fintype U.World]

/-- **Fiber size decreases under refinement** on the unified base.
For any (t+1)-class c', fiberSize(c') ≤ fiberSize(forget c'). -/
theorem ucf_fiberSize_le_under_forget (c' : (U.toRecordFiltration).WorldTypeAt (t + 1)) :
    fiberSize (U.toRecordFiltration) (t + 1) c' ≤
    fiberSize (U.toRecordFiltration) t ((U.toRecordFiltration).forget t c') :=
  fiberSize_le_under_forget (U.toRecordFiltration) t c'

/-- **Strict decrease when refinement is strict** on the unified base.
When the UCF has StrictGrowthAt t, some (t+1)-class has strictly smaller fiber than its forget-image. -/
theorem ucf_fiberSize_lt_under_strict_refinement
    (hStrict : (U.toRecordFiltration).StrictGrowthAt t) :
    ∃ c' : (U.toRecordFiltration).WorldTypeAt (t + 1),
      fiberSize (U.toRecordFiltration) (t + 1) c' <
      fiberSize (U.toRecordFiltration) t ((U.toRecordFiltration).forget t c') :=
  fiberSize_lt_under_strict_refinement (U.toRecordFiltration) t hStrict

end Bridges
end Cosmology
end NemS
