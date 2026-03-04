import ArrowOfTime.Core.Refinement
import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import SelectorStrength.Theorems.BarrierSchema

/-!
# ArrowOfTime.Theorems.SelectionBarrier

**Paper 36: Selection barrier for retrodiction (T4).**

Under diagonal capability (hFP, anti-decider closure), selecting a unique
representative history from a stage world-type (retrodiction) cannot be
total-effective: the "does o hold at the selected world?" predicate is not
decidable in the internal strength class.
-/

set_option autoImplicit false

namespace ArrowOfTime

universe u v

variable {World : Type u} {Obs : Type v} (Filt : RecordFiltration World Obs)
variable [∀ (w : World) (o : Obs), Decidable (Filt.Holds w o)]

/-- A **retrodiction selector** at stage t picks a representative world for each world-type at t. -/
structure RetrodictionSelector (t : Time) where
  sel : Filt.WorldTypeAt t → World
  sec : ∀ qt : Filt.WorldTypeAt t, Filt.toWorldTypeAt t (sel qt) = qt

variable {t : Time} (sel : RetrodictionSelector Filt t)

/-- Predicate: observation o holds at the selector's representative for world-type qt. -/
def retrodictionPred (o : Obs) (qt : Filt.WorldTypeAt t) : Prop :=
  Filt.Holds (sel.sel qt) o

/-- The retrodiction predicate is extensional (respects equality of world-types). -/
theorem retrodictionPred_extensional (o : Obs) :
    SelectorStrength.Extensional (· = ·) (retrodictionPred Filt sel o) := by
  intro qt qt' heq
  rw [heq]

/-- **Selection barrier for retrodiction**: Under the barrier premises (hFP, AntiClosed),
if the predicate "o holds at selected representative" is nontrivial (at least two
world-types differ on o), then the indicator function is not in strength Sbool. -/
theorem selection_barrier_retrodiction
    (o : Obs)
    (qtTrue : Filt.WorldTypeAt t) (htTrue : retrodictionPred Filt sel o qtTrue)
    (qtFalse : Filt.WorldTypeAt t) (htFalse : ¬ retrodictionPred Filt sel o qtFalse)
    (Sbool : SelectorStrength.Strength (Filt.WorldTypeAt t) Bool)
    (Sα : SelectorStrength.Strength (Filt.WorldTypeAt t) (Filt.WorldTypeAt t))
    (hAnti : SelectorStrength.AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : Filt.WorldTypeAt t → Filt.WorldTypeAt t, Sα F → ∃ d : Filt.WorldTypeAt t, d = F d) :
    ¬ Sbool (fun qt => decide (Filt.Holds (sel.sel qt) o)) := by
  set T := retrodictionPred Filt sel o
  have hExt : SelectorStrength.Extensional (· = ·) T := retrodictionPred_extensional Filt sel o
  have hNontriv : SelectorStrength.Nontrivial T := ⟨⟨qtTrue, htTrue⟩, ⟨qtFalse, htFalse⟩⟩
  intro hS
  have hDec : SelectorStrength.DecidableAt Sbool T := by
    refine ⟨fun qt => decide (Filt.Holds (sel.sel qt) o), hS, ?_⟩
    intro qt
    simp only [T, retrodictionPred]
    constructor
    · exact of_decide_eq_true
    · exact decide_eq_true
  exact SelectorStrength.no_total_decider_at_strength_nontrivial (· = ·) T hExt hNontriv
    Sbool Sα hAnti hFP hDec

end ArrowOfTime
