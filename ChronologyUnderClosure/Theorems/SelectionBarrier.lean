import ChronologyUnderClosure.Core.RecordDynamics
import Closure.Core.ObsSemantics
import Closure.Core.Selector
import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import SelectorStrength.Theorems.BarrierSchema

/-!
# ChronologyUnderClosure.Theorems.SelectionBarrier

**Paper 36: Selection barrier for chronology.**

Under diagonal capability (hFP, anti-decider closure), selecting among
world-types (e.g. self-consistent loops) cannot be total-effective: the
"which loop" indicator function is not in the strength class Sbool.
-/

set_option autoImplicit false

namespace ChronologyUnderClosure

universe u v

variable {World : Type u} {Obs : Type v} (S : Closure.ObsSemantics World Obs)
variable [∀ (w : World) (o : Obs), Decidable (S.Holds w o)]

/-- For a selector `sel` and observation `o`, the predicate "o holds at the selected world for type t". -/
def loopPred (sel : Closure.Selector S) (o : Obs) (t : S.WorldType) : Prop :=
  S.Holds (sel.sel t) o

/-- The loop predicate is extensional for equality on world-types. -/
theorem loopPred_extensional (sel : Closure.Selector S) (o : Obs) :
    SelectorStrength.Extensional (· = ·) (loopPred S sel o) := by
  intro t t' h
  simp only [loopPred]
  rw [h]

/-- **Selection barrier for chronology**: Under the barrier premises (hFP, AntiClosed),
the "which world-type has o at selector output" function cannot be in strength Sbool
when the predicate is nontrivial (at least two world-types disagree on o). -/
theorem selection_barrier_chronology
    (sel : Closure.Selector S) (o : Obs)
    (tTrue : S.WorldType) (htTrue : loopPred S sel o tTrue)
    (tFalse : S.WorldType) (htFalse : ¬ loopPred S sel o tFalse)
    (Sbool : SelectorStrength.Strength S.WorldType Bool)
    (Sα : SelectorStrength.Strength S.WorldType S.WorldType)
    (hAnti : SelectorStrength.AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : S.WorldType → S.WorldType, Sα F → ∃ d : S.WorldType, d = F d) :
    ¬ Sbool (fun t => decide (S.Holds (sel.sel t) o)) := by
  intro hS
  set T := loopPred S sel o with hTDef
  have hExt : SelectorStrength.Extensional (· = ·) T := loopPred_extensional S sel o
  have hNontriv : SelectorStrength.Nontrivial T := ⟨⟨tTrue, htTrue⟩, ⟨tFalse, htFalse⟩⟩
  have hDec : SelectorStrength.DecidableAt Sbool T := by
    refine ⟨fun t => decide (S.Holds (sel.sel t) o), hS, ?_⟩
    intro t
    simp only [T, loopPred]
    constructor
    · exact of_decide_eq_true
    · exact decide_eq_true
  exact SelectorStrength.no_total_decider_at_strength_nontrivial (· = ·) T hExt hNontriv Sbool Sα hAnti hFP hDec

end ChronologyUnderClosure
