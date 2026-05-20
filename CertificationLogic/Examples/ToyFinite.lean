import CertificationLogic.Core.Formulas
import CertificationLogic.Core.CertifiableAt
import CertificationLogic.Theorems.CapstoneSoundness
import CertificationLogic.Theorems.CapstoneCompleteness
import CertificationLogic.Core.Protocols
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import InstitutionalEpistemics.Core.Roles

/-!
# CertificationLogic.Examples.ToyFinite — Paper 50 Capstone

Fin 4 instance space, two roles (r0 covers {0,1}, r1 covers {2,3}), union protocol.
Full equivalence: ⊢_S C ↔ CertifiableAt(cov, S, C).
-/

set_option autoImplicit false

namespace CertificationLogic.Examples

open CertificationLogic
open InstitutionalEpistemics

/-- Instance space: four elements. -/
def toyInstance : Type := Fin 4

instance : Fintype toyInstance := inferInstance
instance : DecidableEq toyInstance := inferInstance

/-- Two roles. -/
def toyN : ℕ := 2

instance : DecidableEq (Role toyN) := inferInstance

/-- Coverage: role 0 covers {0,1}, role 1 covers {2,3}. -/
def toyCov : Role toyN → Finset toyInstance := fun r =>
  match r.idx.val with
  | 0 => {(0 : Fin 4), 1}
  | _ => {(2 : Fin 4), 3}

/-- Single stratum. -/
def toyStratum : Type := Unit

/-- Full protocol coverage = union = all four. -/
theorem toy_full_coverage :
    protocolCoverage (CertificationLogic.canonicalRoleAssign toyCov)
      (Prot.union (Prot.atom (Role.mk ⟨0, by omega⟩)) (Prot.atom (Role.mk ⟨1, by omega⟩))) =
      Finset.univ := by
  ext a
  simp only [protocolCoverage, coverage_union, coverage_atom,
    CertificationLogic.coverage_canonicalVerifier, Finset.mem_union, Finset.mem_univ, toyCov]
  fin_cases a <;> simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]

/-- **Toy soundness:** derivable implies certifiable. -/
theorem toy_soundness (C : Finset toyInstance)
    (h : @Derivable Unit toyCov (axFromCov toyCov) () C) :
    @CertifiableAt Unit toyCov () C :=
  @soundness_capstone toyInstance toyN _ _ toyCov () C h

/-- **Toy completeness:** certifiable implies derivable. -/
theorem toy_completeness (C : Finset toyInstance)
    (h : @CertifiableAt Unit toyCov () C) :
    @Derivable Unit toyCov (axFromCov toyCov) () C :=
  @completeness_capstone toyInstance toyN _ _ toyCov () C h

/-- **Toy equivalence:** ⊢ C ↔ CertifiableAt(C). -/
theorem toy_equiv (C : Finset toyInstance) :
    @Derivable Unit toyCov (axFromCov toyCov) () C ↔ @CertifiableAt Unit toyCov () C :=
  ⟨toy_soundness C, toy_completeness C⟩

end CertificationLogic.Examples
