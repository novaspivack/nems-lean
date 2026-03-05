import CertificationLogic.Core.Judgment

/-!
# CertificationLogic.Theorems.Completeness — Paper 50, T50.2

Completeness: CertifiableAt(S, φ) → ⊢_S φ.
-/

set_option autoImplicit false

variable (Formula : Type _)
variable (Stratum : Type _)
variable (ax : CertificationLogic.Ax Formula Stratum)

namespace CertificationLogic

/-- **T50.2 Completeness:** Every certifiable formula is derivable at that stratum. -/
theorem completeness (S : Stratum) (φ : Formula) (h : CertifiableAt Formula Stratum ax S φ) :
    Derivable Formula Stratum ax S φ :=
  match h with
  | CertifiableAt.ax S φ h' => Derivable.ax S φ h'

end CertificationLogic
