import CertificationLogic.Core.Formulas
import CertificationLogic.Core.CertifiableAt
import CertificationLogic.Theorems.CapstoneSoundness
import CertificationLogic.Theorems.CapstoneCompleteness
import CertificationLogic.Core.Protocols
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases
import InstitutionalEpistemics.Core.Roles

/-!
# CertificationLogic.Examples.ToyFinite — Paper 50 Capstone

Fin 4 instance space, two roles (r0 covers {0,1}, r1 covers {2,3}), union protocol.
Full equivalence: ⊢_S C ↔ CertifiableAt(cov, S, C).
-/

set_option autoImplicit false

namespace CertificationLogic.Examples

open CertificationLogic

abbrev toyInstance := Fin 4
abbrev toyN : ℕ := 2

instance : DecidableEq (Role toyN) := inferInstance

/-- Coverage: role 0 covers {0,1}, role 1 covers {2,3}. -/
def toyCov : Role toyN → Finset toyInstance := fun r =>
  match r.idx.val with
  | 0 => {(0 : Fin 4), 1}
  | _ => {(2 : Fin 4), 3}

/-- Full protocol coverage = union = all four. -/
theorem toy_full_coverage :
    protocolCoverage (canonicalRoleAssign toyCov)
      (Prot.union (Prot.atom (Role.mk ⟨0, by decide⟩)) (Prot.atom (Role.mk ⟨1, by decide⟩))) =
      Finset.univ := by
  ext a
  fin_cases a <;>
    simp [protocolCoverage, coverage_union, coverage_atom, mem_coverage, canonicalVerifier,
      canonicalRoleAssign, toyCov, eval]

/-- **Toy soundness:** derivable implies certifiable. -/
theorem toy_finite_soundness (C : Finset toyInstance)
    (h : ProtocolDerivable toyCov (axFromCov toyCov) () C) :
    ProtocolCertifiableAt toyCov () C :=
  soundness_capstone toyCov () C h

/-- **Toy completeness:** certifiable implies derivable. -/
theorem toy_finite_completeness (C : Finset toyInstance)
    (h : ProtocolCertifiableAt toyCov () C) :
    ProtocolDerivable toyCov (axFromCov toyCov) () C :=
  completeness_capstone toyCov () C h

/-- **Toy equivalence:** ⊢ C ↔ ProtocolCertifiableAt(C). -/
theorem toy_finite_equiv (C : Finset toyInstance) :
    ProtocolDerivable toyCov (axFromCov toyCov) () C ↔ ProtocolCertifiableAt toyCov () C :=
  ⟨toy_finite_soundness C, toy_finite_completeness C⟩

end CertificationLogic.Examples
