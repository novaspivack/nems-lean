import NemS.Cosmology.UnifiedClosureFramework
import RecordEntropy.Theorems.Monotonicity

/-!
# NemS.Cosmology.Bridges.ToRecordResolution

**Bridge: Unified filtration ⇒ Record resolution monotonicity.**

Wires the Paper 42 record-entropy monotonicity theorem to the unified closure framework.
The quantity `recordEntropy Filt t = card(WorldTypeAt t)` counts visible equivalence classes;
we call this **record resolution** (not thermodynamic entropy).

**Honest formulation:** No schema assumption. The theorem holds for any UnifiedClosureFramework
with Fintype instances at the relevant stages. Closure-schema universes yield such a filtration,
so the theorem applies in closure settings.
-/

set_option autoImplicit false

namespace NemS
namespace Cosmology
namespace Bridges

open NemS.Cosmology
open ArrowOfTime
open RecordEntropy

/-- **Record resolution monotonicity on the unified base.**

For any UCF with finite world-types at stages t and t+1, the record resolution
(number of visible equivalence classes) is monotone: H(t+1) ≥ H(t).

This quantity is record resolution / visible distinguishability,
not thermodynamic entropy. Thermodynamic interpretation requires additional bridge. -/
theorem ucf_record_resolution_monotone
    {U : UnifiedClosureFramework}
    (t : ArrowOfTime.Time)
    [Fintype ((U.toRecordFiltration).WorldTypeAt t)]
    [Fintype ((U.toRecordFiltration).WorldTypeAt (t + 1))] :
    recordEntropy (U.toRecordFiltration) (t + 1) ≥
    recordEntropy (U.toRecordFiltration) t :=
  recordEntropy_monotone (U.toRecordFiltration) t

end Bridges
end Cosmology
end NemS
