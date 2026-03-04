import ArrowOfTime.Core.RecordFiltration

/-!
# ArrowOfTime.Core.Refinement

**Paper 36: Forgetful maps (arrow as refinement).**

When the record fragment grows, stage equivalence at t+1 refines that at t,
so there is a canonical map WorldTypeAt (t+1) → WorldTypeAt t.
-/

set_option autoImplicit false

namespace ArrowOfTime

universe u v

variable {World : Type u} {Obs : Type v} (Filt : RecordFiltration World Obs)

namespace RecordFiltration

/-- The forgetful map: from world-type at stage (t+1) to world-type at stage t.
Induced by the fact that ObsEqAt (t+1) refines ObsEqAt t. -/
def forget (t : Time) : Filt.WorldTypeAt (t + 1) → Filt.WorldTypeAt t :=
  Quotient.lift (fun w => Filt.toWorldTypeAt t w) (by
    intro w₁ w₂ h
    exact Quotient.sound (Filt.refine t (t + 1) w₁ w₂ (Nat.le_succ t) h))

/-- Coherence: forget (toWorldTypeAt (t+1) w) = toWorldTypeAt t w. -/
theorem forget_coherent (t : Time) (w : World) :
    Filt.forget t (Filt.toWorldTypeAt (t + 1) w) = Filt.toWorldTypeAt t w :=
  rfl

end RecordFiltration

end ArrowOfTime
