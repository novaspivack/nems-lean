import ArrowOfTime.Core.RecordFiltration
import ArrowOfTime.Core.Refinement
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

/-!
# RecordEntropy.Core.EntropyFinite

**Paper 42: Record entropy (finite case).**

For a record filtration with finite stage world-types, define the record entropy
H(t) as the cardinality of WorldTypeAt t (number of observational equivalence classes).
-/

namespace RecordEntropy

universe u v

variable {World : Type u} {Obs : Type v}

open ArrowOfTime
open ArrowOfTime.RecordFiltration

/-- **Record entropy (finite case):** number of world-types at stage t.
Requires Fintype (WorldTypeAt t); in the finite-World setting this holds. -/
def recordEntropy (Filt : RecordFiltration World Obs) (t : Time) [Fintype (Filt.WorldTypeAt t)] :
    Nat :=
  Fintype.card (Filt.WorldTypeAt t)

end RecordEntropy
