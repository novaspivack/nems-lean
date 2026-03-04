import ArrowOfTime.Theorems.ArrowRefinement
import ArrowOfTime.Theorems.NoOverwrite

/-!
# ArrowOfTime.Examples.Toy

**Paper 36: Toy witness for strict refinement and no-overwrite.**

Worlds = pairs of bits (b₀, b₁). Observation false = first bit, true = second bit.
At time 0 only first bit visible; at time 1 both visible.
-/

set_option autoImplicit false

namespace ArrowOfTime

/-- Two bits. -/
def ToyWorld := Bool × Bool

/-- Two observations: false = first bit, true = second bit. -/
def ToyObs := Bool

namespace Toy

/-- Holds: false is first bit, true is second bit. -/
def holds (w : ToyWorld) (o : ToyObs) : Prop :=
  match o with
  | false => w.1
  | true => w.2

/-- Visible at t: first bit (false) always; second bit (true) only when t ≥ 1. -/
def visible (t : Time) (o : ToyObs) : Prop :=
  match o with
  | false => True
  | true => t ≥ 1

theorem visible_mono (t t' : Time) (o : ToyObs) (hle : t ≤ t') (hv : visible t o) :
    visible t' o := by
  unfold visible at hv ⊢
  split <;> try trivial
  exact Nat.le_trans hv hle

/-- Toy record filtration. -/
def filt : RecordFiltration ToyWorld ToyObs where
  Holds := holds
  Visible := visible
  mono := visible_mono

@[simp] theorem filt_Holds (w : ToyWorld) (o : ToyObs) : filt.Holds w o ↔ holds w o := Iff.rfl
@[simp] theorem filt_Visible (t : Time) (o : ToyObs) : filt.Visible t o ↔ visible t o := Iff.rfl

/-- At time 0, (true, true) and (true, false) are equivalent (same first bit). -/
theorem toy_equiv0 (b : Bool) : filt.ObsEqAt 0 (true, b) (true, false) := by
  intro o vo
  cases o <;> simp only [filt_Holds, filt_Visible, holds, visible] at vo ⊢
  trivial

/-- At time 1, (true, true) and (true, false) are not equivalent. -/
theorem toy_neq1 : ¬ filt.ObsEqAt 1 (true, true) (true, false) := by
  intro h
  have := h true (by simp only [filt_Visible, visible]; exact Nat.le_refl 1)
  simp only [filt_Holds, holds] at this
  exact Bool.noConfusion (this.1 trivial)

/-- Strict growth at t=0. -/
theorem toy_strict_growth : filt.StrictGrowthAt 0 := by
  refine ⟨true, by simp only [filt_Visible, visible]; exact Nat.le_refl 1,
    by simp only [filt_Visible, visible]; intro h; exact Nat.not_succ_le_zero 0 h,
    (true, true), (true, false), ?_, ?_⟩
  · exact toy_equiv0 true
  · simp only [filt_Holds, holds]
    exact ⟨fun _ h => Bool.noConfusion h, fun _ => trivial⟩

/-- Dynamics that flips the first bit. -/
def flipB0 : Dynamics ToyWorld := fun w => (¬ w.1, w.2)

/-- Overwrite at t=0. -/
theorem toy_overwrite (b : Bool) : OverwriteAt filt flipB0 0 (true, b) false := by
  refine ⟨trivial, ?_, ?_⟩
  · simp only [filt_Holds, holds]
  · simp only [flipB0, filt_Holds, holds]; intro h; exact Bool.noConfusion h

/-- At time 0, (true, true) and (false, true) are different world-types. -/
theorem toy_not_categorical_at_0 : ¬ CategoricalAt filt 0 := by
  intro h
  have heq : filt.toWorldTypeAt 0 (true, true) = filt.toWorldTypeAt 0 (false, true) :=
    @Subsingleton.elim (filt.WorldTypeAt 0) h _ _
  have hObs : filt.ObsEqAt 0 (true, true) (false, true) := (Quotient.eq (r := filt.obsEqAtSetoid 0)).mp heq
  have := hObs false trivial
  simp only [filt_Holds, holds] at this
  exact Bool.noConfusion (this.1 trivial)

/-- No-overwrite theorem applied. -/
theorem toy_no_overwrite_witness : ¬ CategoricalAt filt 0 :=
  no_overwrite_implies_not_categorical filt flipB0 0 (true, true) false (toy_overwrite true)

end Toy

end ArrowOfTime
