import NemS.Cosmology.UnifiedClosureFramework
import NemS.Cosmology.CosmologicalClosureSchema
import NemS.Observers.RecordStability

/-!
# NemS.Cosmology.StrongCosmologicalClosureSchema

**Extension B: Strengthened schema for the observer/adjudicator arc.**

Adds the Paper 17 premises (Global Record Stability, Nonlocal Coherence Constraints)
to the base CosmologicalClosureSchema. Used by ToAdjudicators to prove
adjudicator network existence under the strengthened closure.
-/

set_option autoImplicit false

namespace NemS
namespace Cosmology

open NemS.Observers

/-- **Strong Cosmological Closure Schema.**

Extends the base schema with Paper 17 premises needed for the adjudicator
infrastructure theorem. Does not add conclusion-shaped predicates.
-/
structure StrongCosmologicalClosureSchema (U : UnifiedClosureFramework) extends CosmologicalClosureSchema U where
  /-- Global record stability (Paper 17). -/
  global_record_stability : GlobalRecordStability U.toFramework
  /-- Nonlocal coherence constraints (Paper 17). -/
  nonlocal_coherence : NonlocalCoherenceConstraints U.toFramework

end Cosmology
end NemS
