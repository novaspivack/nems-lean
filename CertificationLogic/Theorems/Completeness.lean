import CertificationLogic.Core.Judgment

/-!
# CertificationLogic.Theorems.Completeness — Paper 50, T50.2

Completeness: CertifiableAt(S, φ) → ⊢_S φ.
-/

set_option autoImplicit false

variable (Formula : Type _)
variable (Stratum : Type _)
variable (ax : CertificationLogic.Judgment.Ax Formula Stratum)

namespace CertificationLogic

open Judgment

/-- **T50.2 Completeness:** Every certifiable formula is derivable at that stratum. -/
theorem completeness (S : Stratum) (φ : Formula) (h : CertifiableAt Formula Stratum ax S φ) :
    Derivable Formula Stratum ax S φ := by
  match h with
  | .ax _ _ hax => exact Derivable.ax S φ hax

end CertificationLogic
