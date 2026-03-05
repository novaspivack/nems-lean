import RecordEntropy.Core.EntropyFinite
import RecordEntropy.Theorems.Monotonicity
import RecordEntropy.Theorems.NoncomputabilityBarrier
import ArrowOfTime.Examples.Toy
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false

/-!
# RecordEntropy.Examples.ToyEntropy

**Paper 42: Toy witness for record entropy.**

Two-bit filtration (ArrowOfTime.Toy): Fintype instances for WorldTypeAt 0 and 1,
monotonicity, strict growth at t=0, and barrier predicate nontrivial.
-/

namespace RecordEntropy

open ArrowOfTime
open ArrowOfTime.RecordFiltration
open ArrowOfTime.Toy

attribute [local instance] Classical.propDecidable

/-- ToyWorld = Bool × Bool is finite. -/
instance toyWorldFintype : Fintype ToyWorld :=
  show Fintype (Bool × Bool) from inferInstance

/-- At time 0, Toy quotient has 2 world-types (first bit distinguishes). -/
noncomputable instance filtWorldTypeAt0Fintype : Fintype (filt.WorldTypeAt 0) :=
  Quotient.fintype (filt.obsEqAtSetoid 0)

/-- At time 1, Toy quotient has 4 world-types (both bits visible). -/
noncomputable instance filtWorldTypeAt1Fintype : Fintype (filt.WorldTypeAt 1) :=
  Quotient.fintype (filt.obsEqAtSetoid 1)

/-- WorldTypeAt (0+1) = WorldTypeAt 1 for Toy. -/
noncomputable instance filtWorldTypeAt0Plus1Fintype : Fintype (filt.WorldTypeAt (0 + 1)) :=
  filtWorldTypeAt1Fintype

/-- Record entropy is monotone for Toy at t=0. -/
theorem toy_entropy_monotone : recordEntropy filt 1 ≥ recordEntropy filt 0 :=
  recordEntropy_monotone filt 0

/-- Record entropy is strictly increasing for Toy at t=0. -/
theorem toy_entropy_strict : recordEntropy filt 1 > recordEntropy filt 0 :=
  recordEntropy_strict filt 0 toy_strict_growth

/-- The entropy claim for Toy at t=0 is nontrivial. -/
theorem toy_entropy_claim_nontrivial : SelectorStrength.Nontrivial (entropyClaim filt 0) :=
  entropyClaim_nontrivial filt 0

/-- Barrier applies to Toy entropy claim at t=0 under hFP and anti-closure. -/
theorem toy_no_total_decider_entropy
    (Sbool : SelectorStrength.Strength Nat Bool) (Sα : SelectorStrength.Strength Nat Nat)
    (hAnti : SelectorStrength.AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : Nat → Nat, Sα F → ∃ d : Nat, d = F d) :
    ¬ SelectorStrength.DecidableAt Sbool (entropyClaim filt 0) :=
  no_total_decider_entropy filt 0 Sbool Sα hAnti hFP

end RecordEntropy
