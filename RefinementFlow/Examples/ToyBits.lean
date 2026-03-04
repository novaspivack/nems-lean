import RefinementFlow.Core.RefinementFlow
import ArrowOfTime.Theorems.ArrowRefinement
import ArrowOfTime.Examples.Toy

set_option autoImplicit false

/-!
# RefinementFlow.Examples.ToyBits

**Paper 41: Toy witness for refinement flow.**

Reuses ArrowOfTime.Toy (two-bit world, visibility at t=0 and t=1)
and exhibits strict refinement at t=0.
-/

namespace RefinementFlow

open ArrowOfTime
open ArrowOfTime.RecordFiltration
open ArrowOfTime.Toy

/-- The toy filtration from Paper 36 (two bits). -/
abbrev toyFilt : RecordFiltration ToyWorld ToyObs := filt

/-- Strict growth at t=0 (imported from ArrowOfTime.Toy). -/
theorem toy_strict_growth : toyFilt.StrictGrowthAt 0 := ArrowOfTime.Toy.toy_strict_growth

/-- Iterated forget from stage 1 to 0 sends quotient of w to quotient of w at 0. -/
theorem toy_forgetFromTo_01 (w : ToyWorld) :
    forgetFromTo toyFilt 0 1 (Nat.zero_le 1) (toyFilt.toWorldTypeAt 1 w) = toyFilt.toWorldTypeAt 0 w :=
  forgetFromTo_coherent toyFilt 0 1 (Nat.zero_le 1) w

end RefinementFlow
