import CertificationLogic.Core.Judgment

/-!
# CertificationLogic.Theorems.Soundness — Paper 50, T50.1

Soundness: ⊢_S φ → CertifiableAt(S, φ).
-/

set_option autoImplicit false

variable (Formula : Type _)
variable (Stratum : Type _)
variable (ax : CertificationLogic.Ax Formula Stratum)

namespace CertificationLogic

/-- **T50.1 Soundness:** Every derivable formula is certifiable at that stratum. -/
theorem soundness (S : Stratum) (φ : Formula) (h : Derivable Formula Stratum ax S φ) :
    CertifiableAt Formula Stratum ax S φ :=
  match h with
  | Derivable.ax S φ h' => CertifiableAt.ax S φ h'

end CertificationLogic
