/-!
# CertificationLogic.Core.Judgment — Paper 50

Stratified certification logic: formulas, strata, axioms, derivability (⊢_S), and certifiability.
-/

set_option autoImplicit false

namespace CertificationLogic

/-- Axioms at a given stratum (base certifiable formulas). -/
def Ax (Formula : Type _) (Stratum : Type _) : Type _ := Stratum → Formula → Prop

/-- **Derivable at stratum S** (⊢_S φ): inductive proof system (axiom rule only; extend with more rules). -/
inductive Derivable (Formula : Type _) (Stratum : Type _) (ax : Ax Formula Stratum) : Stratum → Formula → Prop
  | ax (S : Stratum) (φ : Formula) (h : ax S φ) : Derivable Formula Stratum ax S φ

/-- **Certifiable at stratum S**: semantic side—closure of axioms (same structure as derivability). -/
inductive CertifiableAt (Formula : Type _) (Stratum : Type _) (ax : Ax Formula Stratum) : Stratum → Formula → Prop
  | ax (S : Stratum) (φ : Formula) (h : ax S φ) : CertifiableAt Formula Stratum ax S φ

end CertificationLogic
