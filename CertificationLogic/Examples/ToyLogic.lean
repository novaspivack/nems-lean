import CertificationLogic.Core.Judgment
import CertificationLogic.Theorems.Soundness
import CertificationLogic.Theorems.Completeness
import Mathlib.Data.Fin.Basic

/-!
# CertificationLogic.Examples.ToyLogic — Paper 50

Minimal toy: Fin 2 formulas, one stratum (Unit), axioms at 0; soundness and completeness hold.
-/

set_option autoImplicit false

namespace CertificationLogic.Examples

/-- Toy formula space: two atoms. -/
def ToyFormula := Fin 2

/-- Toy stratum: single level. -/
def ToyStratum := Unit

/-- Axioms: only formula 0 is an axiom at the single stratum. -/
def toyAx : CertificationLogic.Ax ToyFormula ToyStratum :=
  fun _ φ => φ.val = 0

theorem toy_soundness (φ : ToyFormula) (h : CertificationLogic.Derivable ToyFormula ToyStratum toyAx () φ) :
    CertificationLogic.CertifiableAt ToyFormula ToyStratum toyAx () φ :=
  CertificationLogic.soundness ToyFormula ToyStratum toyAx () φ h

theorem toy_completeness (φ : ToyFormula) (h : CertificationLogic.CertifiableAt ToyFormula ToyStratum toyAx () φ) :
    CertificationLogic.Derivable ToyFormula ToyStratum toyAx () φ :=
  CertificationLogic.completeness ToyFormula ToyStratum toyAx () φ h

/-- Equivalence: ⊢ φ ↔ CertifiableAt(φ) in the toy. -/
theorem toy_equiv (φ : ToyFormula) :
    CertificationLogic.Derivable ToyFormula ToyStratum toyAx () φ ↔
      CertificationLogic.CertifiableAt ToyFormula ToyStratum toyAx () φ :=
  ⟨fun h => toy_soundness φ h, fun h => toy_completeness φ h⟩

end CertificationLogic.Examples
