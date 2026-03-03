import Reflection.Core.SRI_R
import Reflection.Theorems.DiagonalClosure

/-!
# Reflection.Hierarchy.Examples

Separation examples: when R = allRepresentable we recover full MFP-1.
-/

set_option autoImplicit false

namespace Reflection

namespace Hierarchy

variable {Obj : Type u} {Code : Type v}

/-- Recovery: SRI_R with R = allRepresentable and DiagClosed yields
the same fixed-point theorem as SRI0'. -/
theorem allRepresentable_restricted_fixed_point
    [S : SRI_R Obj Code (allRepresentable (Obj := Obj) (Code := Code))]
    (hDiag : DiagClosed (allRepresentable (Obj := Obj) (Code := Code)))
    (F : Code → Obj) :
    ∃ p : Obj, S.Equiv p (F (S.quote p)) :=
  restricted_master_fixed_point hDiag F trivial

end Hierarchy

end Reflection
