import ArrowOfTime.Core.Refinement

/-!
# ArrowOfTime.Theorems.ArrowRefinement

**Paper 36: Arrow as refinement (T1), strict refinement (Toy A).**

Canonical forgetful map exists; strict record growth implies forget is not injective.
-/

set_option autoImplicit false

namespace ArrowOfTime

universe u v

variable {World : Type u} {Obs : Type v} (Filt : RecordFiltration World Obs)

namespace RecordFiltration

/-- **Strict record growth at t**: there is an observation o visible at t+1 but not at t,
and two worlds that agree at stage t but disagree on o at stage t+1. -/
def StrictGrowthAt (t : Time) : Prop :=
  ∃ o : Obs, Filt.Visible (t + 1) o ∧ ¬ Filt.Visible t o ∧
    ∃ w₁ w₂ : World, Filt.ObsEqAt t w₁ w₂ ∧ (Filt.Holds w₁ o ↔ ¬ Filt.Holds w₂ o)

/-- **Strict refinement**: when record growth is strict at t, the forgetful map
from WorldTypeAt (t+1) to WorldTypeAt t is not injective: two distinct (t+1)-classes
map to the same t-class. -/
theorem strict_refinement (t : Time) (hStrict : Filt.StrictGrowthAt t) :
    ∃ a b : Filt.WorldTypeAt (t + 1), a ≠ b ∧ Filt.forget t a = Filt.forget t b := by
  obtain ⟨o, hVis, _, w₁, w₂, heqAt, hdiff⟩ := hStrict
  use Filt.toWorldTypeAt (t + 1) w₁, Filt.toWorldTypeAt (t + 1) w₂
  constructor
  · intro heq
    have hq : Filt.ObsEqAt (t + 1) w₁ w₂ := Quotient.exact heq
    have hoo : Filt.Visible (t + 1) o := hVis
    have h12 : (Filt.Holds w₁ o ↔ Filt.Holds w₂ o) := hq o hoo
    by_cases h1 : Filt.Holds w₁ o
    · have hn2 : ¬ Filt.Holds w₂ o := hdiff.mp h1
      exact hn2 (h12.mp h1)
    · have h2 : Filt.Holds w₂ o := by
        by_contra hn2
        exact h1 (hdiff.mpr hn2)
      exact h1 (h12.mpr h2)
  · simp only [forget_coherent]
    exact Quotient.sound heqAt

end RecordFiltration

end ArrowOfTime
