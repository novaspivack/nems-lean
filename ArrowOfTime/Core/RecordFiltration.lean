import NemS.Prelude
import Closure.Core.ObsSemantics

/-!
# ArrowOfTime.Core.RecordFiltration

**Paper 36: Record filtration semantics.**

Time-indexed record fragments: Visible(t, o) means observation o is
accessible by time t. Stage equivalence and stage world-types.
-/

set_option autoImplicit false

namespace ArrowOfTime

universe u v w

variable {World : Type u} {Obs : Type v}

/-- Time index (stages of record availability). -/
abbrev Time := Nat

/-- A record filtration extends observational semantics with a visibility predicate:
at time t, which observations are "available". Monotone: if t ≤ t' then Visible t o → Visible t' o. -/
structure RecordFiltration (World : Type u) (Obs : Type v) extends Closure.ObsSemantics World Obs where
  Visible : Time → Obs → Prop
  mono : ∀ t t' (o : Obs), t ≤ t' → Visible t o → Visible t' o

variable (Filt : RecordFiltration World Obs)

namespace RecordFiltration

/-- Stage observational equivalence: w₁ ~_t w₂ iff they agree on all observations visible at t. -/
def ObsEqAt (t : Time) (w₁ w₂ : World) : Prop :=
  ∀ o : Obs, Filt.Visible t o → (Filt.Holds w₁ o ↔ Filt.Holds w₂ o)

namespace ObsEqAt

theorem refl (t : Time) (w : World) : Filt.ObsEqAt t w w :=
  fun _ _ => Iff.rfl

theorem symm {t : Time} {w₁ w₂ : World} (h : Filt.ObsEqAt t w₁ w₂) : Filt.ObsEqAt t w₂ w₁ :=
  fun o vo => (h o vo).symm

theorem trans {t : Time} {w₁ w₂ w₃ : World} (h₁ : Filt.ObsEqAt t w₁ w₂) (h₂ : Filt.ObsEqAt t w₂ w₃) :
    Filt.ObsEqAt t w₁ w₃ :=
  fun o vo => (h₁ o vo).trans (h₂ o vo)

theorem isEquivalence (t : Time) : Equivalence (Filt.ObsEqAt t) :=
  ⟨refl Filt t, symm Filt, trans Filt⟩

end ObsEqAt

/-- Setoid at stage t. -/
def obsEqAtSetoid (t : Time) : Setoid World where
  r := Filt.ObsEqAt t
  iseqv := ObsEqAt.isEquivalence Filt t

/-- World-type at stage t: quotient of World by stage equivalence. -/
def WorldTypeAt (t : Time) : Type u :=
  Quotient (Filt.obsEqAtSetoid t)

/-- Quotient map at stage t. -/
def toWorldTypeAt (t : Time) (w : World) : Filt.WorldTypeAt t :=
  Quotient.mk (Filt.obsEqAtSetoid t) w

/-- Later stage refines earlier: if t ≤ t', then ObsEqAt t' implies ObsEqAt t. -/
theorem refine (t t' : Time) (w₁ w₂ : World) (hle : t ≤ t') (h : Filt.ObsEqAt t' w₁ w₂) :
    Filt.ObsEqAt t w₁ w₂ :=
  fun o vo => h o (Filt.mono t t' o hle vo)

end RecordFiltration

end ArrowOfTime
