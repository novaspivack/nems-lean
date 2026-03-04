import Reflection.Theorems.DiagonalClosure
import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import SelectorStrength.Theorems.BarrierSchema

/-!
# SelectorStrength.Bridge.Reflection

**Reflection supplies the fixed-point premise (Paper 29 + Paper 28).**

When we have SRI_R with a diagonally closed R, Reflection's
`restricted_master_fixed_point` gives the fixed-point principle for all F ∈ R.
We can therefore instantiate the barrier schema using Reflection.
-/

set_option autoImplicit false

namespace SelectorStrength

universe u v

variable {Obj : Type u} {Code : Type v} {R : (Code → Obj) → Prop}
  [sri : Reflection.SRI_R Obj Code R]

/-- When R is diagonally closed, every F ∈ R has a mixed fixed point (Paper 28).
This is the hFP premise for the barrier schema when Sα corresponds to R. -/
theorem reflection_supplies_hFP (hDiag : Reflection.DiagClosed R) (F : Code → Obj) (hF : R F) :
    ∃ p : Obj, sri.Equiv p (F (sri.quote p)) :=
  Reflection.restricted_master_fixed_point hDiag F hF

/-- **Barrier from Reflection**: The fixed-point principle required by the barrier
schema is supplied by Reflection when DiagClosed R holds: every F ∈ R has a
mixed fixed point. -/
theorem barrier_premise_from_reflection (hDiag : Reflection.DiagClosed R) :
    ∀ F : Code → Obj, R F → ∃ p : Obj, sri.Equiv p (F (sri.quote p)) :=
  fun F hF => reflection_supplies_hFP hDiag F hF

end SelectorStrength
