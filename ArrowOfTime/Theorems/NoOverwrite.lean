import ArrowOfTime.Core.RecordFiltration

/-!
# ArrowOfTime.Theorems.NoOverwrite

**Paper 36: No-overwrite implies non-categoricity (T2).**

If a dynamics step F overwrites a stable record (visible at t), then the
stage semantics at t is not categorical (multiple world-types).
-/

set_option autoImplicit false

namespace ArrowOfTime

universe u v

variable {World : Type u} {Obs : Type v} (Filt : RecordFiltration World Obs)

/-- A dynamics step (e.g. feedback, time-reversal attempt). -/
def Dynamics (World : Type u) : Type u := World → World

variable (F : Dynamics World)

/-- **Overwrite at stage t**: some observation o visible at t holds at w but not at F w. -/
def OverwriteAt (t : Time) (w : World) (o : Obs) : Prop :=
  Filt.Visible t o ∧ Filt.Holds w o ∧ ¬ Filt.Holds (F w) o

/-- **Categorical at stage t**: at most one world-type at t. -/
def CategoricalAt (t : Time) : Prop :=
  Subsingleton (Filt.WorldTypeAt t)

/-- **No-overwrite theorem**: overwrite at stage t implies the stage semantics is not categorical. -/
theorem no_overwrite_implies_not_categorical (t : Time) (w : World) (o : Obs)
    (hOver : OverwriteAt Filt F t w o) :
    ¬ CategoricalAt Filt t := by
  intro hCat
  have heq : Filt.toWorldTypeAt t w = Filt.toWorldTypeAt t (F w) :=
    @Subsingleton.elim (Filt.WorldTypeAt t) hCat (Filt.toWorldTypeAt t w) (Filt.toWorldTypeAt t (F w))
  have hObsEq : Filt.ObsEqAt t w (F w) := (Quotient.eq (r := Filt.obsEqAtSetoid t)).mp heq
  obtain ⟨hVis, hHold, hNot⟩ := hOver
  have hHold' : Filt.Holds (F w) o ↔ Filt.Holds w o := (hObsEq o hVis).symm
  exact hNot (hHold'.mpr hHold)

end ArrowOfTime
