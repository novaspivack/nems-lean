import CertificationLogic.Core.Formulas
import CertificationLogic.Core.Protocols
import Mathlib.Data.Finset.Basic

/-!
# CertificationLogic.Core.CertifiableAt — Paper 50 Capstone

Semantic CertifiableAt: exists admissible protocol at strength S covering claim set C.
-/

set_option autoImplicit false

namespace CertificationLogic

variable {Instance : Type*} [Fintype Instance] [DecidableEq Instance]
variable {n : ℕ} [DecidableEq (Role n)]

/-- Role assignment R is consistent with coverage map cov when each R r has
  coverage exactly cov r. -/
def ConsistentWith (cov : Role n → Finset Instance) (R : Role n → Verifier Instance) : Prop :=
  ∀ r, coverage (R r) = cov r

/-- Canonical role assignment from a coverage map. -/
def canonicalRoleAssign (cov : Role n → Finset Instance) : Role n → Verifier Instance :=
  fun r => canonicalVerifier (cov r)

theorem ConsistentWith_canonical (cov : Role n → Finset Instance) :
    ConsistentWith cov (canonicalRoleAssign cov) :=
  fun r => coverage_canonicalVerifier (cov r)

/-- Any consistent R has the same protocol coverage as the canonical assignment. -/
theorem protocolCoverage_eq_of_ConsistentWith (cov : Role n → Finset Instance)
    (R : Role n → Verifier Instance) (hR : ConsistentWith cov R) (P : Prot n) :
    protocolCoverage R P = protocolCoverage (canonicalRoleAssign cov) P :=
  protocolCoverage_eq_of_same_coverage R (canonicalRoleAssign cov)
    (fun r => (hR r).trans (coverage_canonicalVerifier (cov r)).symm) P

/-- **CertifiableAt**(cov, S, C): semantic—exists protocol P and role assignment R
  consistent with cov such that C ⊆ protocolCoverage R P.
  (Stratum S abstract; for single-stratum, use Unit.) -/
def CertifiableAt {Stratum : Type*} (cov : Role n → Finset Instance) (_S : Stratum)
    (C : Finset Instance) : Prop :=
  ∃ (P : Prot n) (R : Role n → Verifier Instance),
    ConsistentWith cov R ∧ C ⊆ protocolCoverage R P

end CertificationLogic
