import CertificationLogic.Core.Formulas
import CertificationLogic.Core.Protocols
import Mathlib.Data.Finset.Basic

/-!
# CertificationLogic.Core.CertifiableAt — Paper 50 Capstone

Semantic CertifiableAt: exists admissible protocol at strength S covering claim set C.
-/

set_option autoImplicit false

variable (Instance : Type*) [Fintype Instance] [DecidableEq Instance]
variable (n : ℕ) [DecidableEq (InstitutionalEpistemics.Role n)]

namespace CertificationLogic

open CertificationLogic.Protocols

variable {Instance n}

/-- Role assignment R is consistent with coverage map cov when each R r has
  coverage exactly cov r. -/
def ConsistentWith (cov : CovMap Instance n) (R : Protocols.RoleAssign) : Prop :=
  ∀ r, CertificationLogic.coverage (R r) = cov r

/-- Canonical role assignment from a coverage map. -/
def canonicalRoleAssign (cov : CovMap Instance n) : Protocols.RoleAssign :=
  fun r => CertificationLogic.canonicalVerifier (cov r)

theorem ConsistentWith_canonical (cov : CovMap Instance n) :
    ConsistentWith cov (canonicalRoleAssign cov) :=
  fun r => CertificationLogic.coverage_canonicalVerifier (cov r)

/-- Any consistent R has the same protocol coverage as the canonical assignment. -/
theorem protocolCoverage_eq_of_ConsistentWith (cov : CovMap Instance n) (R : Protocols.RoleAssign)
    (hR : ConsistentWith cov R) (P : Protocols.Prot n) :
    Protocols.protocolCoverage R P = Protocols.protocolCoverage (canonicalRoleAssign cov) P :=
  Protocols.protocolCoverage_eq_of_same_coverage R (canonicalRoleAssign cov)
    (fun r => (hR r).symm) P

/-- **CertifiableAt**(cov, S, C): semantic—exists protocol P and role assignment R
  consistent with cov such that C ⊆ protocolCoverage R P.
  (Stratum S abstract; for single-stratum, use Unit.) -/
def CertifiableAt {Stratum : Type*} (cov : CovMap Instance n) (_S : Stratum)
    (C : Formula Instance) : Prop :=
  ∃ (P : Protocols.Prot n) (R : Protocols.RoleAssign),
    ConsistentWith cov R ∧ C ⊆ Protocols.protocolCoverage R P

end CertificationLogic
