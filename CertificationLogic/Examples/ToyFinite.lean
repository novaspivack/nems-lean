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
open CertificationLogic.Protocols
open InstitutionalEpistemics

/-- Instance space: four elements. -/
def toyInstance : Type := Fin 4

instance : Fintype toyInstance := inferInstance
instance : DecidableEq toyInstance := inferInstance

/-- Two roles. -/
def toyN : ℕ := 2

instance : DecidableEq (Role toyN) := inferInstance

/-- Coverage: role 0 covers {0,1}, role 1 covers {2,3}. -/
def toyCov : CovMap toyInstance toyN := fun r =>
  match r.idx.val with
  | 0 => {(0 : Fin 4), 1}
  | _ => {(2 : Fin 4), 3}

/-- Single stratum. -/
def toyStratum : Type := Unit

/-- Full protocol coverage = union = all four. -/
theorem toy_full_coverage :
    Protocols.protocolCoverage (CertificationLogic.canonicalRoleAssign toyInstance toyN toyCov)
      (Prot.union (Prot.atom (Role.mk ⟨0, by omega⟩)) (Prot.atom (Role.mk ⟨1, by omega⟩))) = Finset.univ := by
  ext a
  simp only [Protocols.protocolCoverage, Protocols.coverage_union, Protocols.coverage_atom,
    CertificationLogic.coverage_canonicalVerifier, Finset.mem_union, Finset.mem_univ, toyCov]
  fin_cases a <;> simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]

/-- **Toy soundness:** derivable implies certifiable. -/
theorem toy_soundness (C : Formula toyInstance) (h : Derivable toyCov (axFromCov toyCov) () C) :
    CertifiableAt toyInstance toyN toyCov () C :=
  CertificationLogic.soundness_capstone toyCov () C h

/-- **Toy completeness:** certifiable implies derivable. -/
theorem toy_completeness (C : Formula toyInstance) (h : CertifiableAt toyInstance toyN toyCov () C) :
    Derivable toyCov (axFromCov toyCov) () C :=
  CertificationLogic.completeness_capstone toyCov () C h

/-- **Toy equivalence:** ⊢ C ↔ CertifiableAt(C). -/
theorem toy_equiv (C : Formula toyInstance) :
    Derivable toyCov (axFromCov toyCov) () C ↔ CertifiableAt toyInstance toyN toyCov () C :=
  ⟨toy_soundness C, toy_completeness C⟩

end CertificationLogic.Examples
