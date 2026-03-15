import AdmissibleContinuation.Core.ContinuationSystem

/-!
# AdmissibleContinuation.Theorems.ClosureCompatibleContinuation

Closure-compatible burden-bearing implies admissible continuation (Program II).
-/

set_option autoImplicit false

namespace AdmissibleContinuation

open ContinuationSystem

/-- **Closure-compatible continuation theorem.**
ClosureCompatible ∧ BurdenBearing ⇒ AdmissibleContinuation. -/
theorem closure_compatible_continuation (CS : ContinuationSystem)
    (hCC : CS.ClosureCompatible) (hBB : CS.BurdenBearing) :
    CS.AdmissibleContinuation :=
  ⟨hCC, hBB⟩

end AdmissibleContinuation
