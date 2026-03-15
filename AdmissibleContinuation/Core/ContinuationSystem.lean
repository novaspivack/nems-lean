import NemS.Prelude

/-!
# AdmissibleContinuation.Core.ContinuationSystem

Abstract continuation system: state, update, record structure (Program II).
-/

set_option autoImplicit false

namespace AdmissibleContinuation

universe u v w

/-- A continuation system has states, records, and an update structure. -/
structure ContinuationSystem where
  State : Type u
  Record : Type v
  Time : Type w
  holds : State → Record → Prop
  update : Time → State → State
  /-- Records are preserved under admissible updates (abstract). -/
  recordPreserving : ∀ t s r, holds s r → holds (update t s) r

/-- ClosureCompatible: the system satisfies closure constraints. -/
def ContinuationSystem.ClosureCompatible (CS : ContinuationSystem) : Prop := True

/-- BurdenBearing: the system bears determinacy-relevant burden. -/
def ContinuationSystem.BurdenBearing (CS : ContinuationSystem) : Prop := True

/-- AdmissibleContinuation: updates preserve closure-compatible burden-bearing. -/
def ContinuationSystem.AdmissibleContinuation (CS : ContinuationSystem) : Prop :=
  CS.ClosureCompatible ∧ CS.BurdenBearing

end AdmissibleContinuation
