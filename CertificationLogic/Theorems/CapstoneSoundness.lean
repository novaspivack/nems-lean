import CertificationLogic.Core.Formulas
import CertificationLogic.Core.CertifiableAt
import CertificationLogic.Core.Protocols
import Mathlib.Data.Finset.Basic

/-!
# CertificationLogic.Theorems.CapstoneSoundness — Paper 50 Capstone, T50.1

Soundness: ⊢_S C → CertifiableAt(cov, S, C) for protocol-based semantics.
-/

set_option autoImplicit false

namespace CertificationLogic

variable {Instance : Type*} [Fintype Instance] [DecidableEq Instance]
variable {n : ℕ} [DecidableEq (Role n)]

/-- **T50.1 Soundness (capstone):** Every derivable claim set is certifiable. -/
theorem soundness_capstone {Stratum : Type*} (cov : Role n → Finset Instance) (S : Stratum)
    (C : Finset Instance) (h : Derivable cov (axFromCov cov) S C) :
    CertifiableAt cov S C := by
  induction h with
  | ax S C hax =>
    obtain ⟨r, hC⟩ := hax
    refine ⟨Prot.atom r, canonicalRoleAssign cov, ConsistentWith_canonical cov, ?_⟩
    have hcanon : coverage (canonicalRoleAssign cov r) = cov r := coverage_canonicalVerifier (cov r)
    rw [coverage_atom, hcanon]
    exact hC
  | union S C₁ C₂ _ _ ih1 ih2 =>
    obtain ⟨P₁, R₁, hR1, hC1⟩ := ih1
    obtain ⟨P₂, R₂, hR2, hC2⟩ := ih2
    have hcov1 : C₁ ⊆ protocolCoverage (canonicalRoleAssign cov) P₁ := by
      rw [← protocolCoverage_eq_of_ConsistentWith cov R₁ hR1 P₁]
      exact hC1
    have hcov2 : C₂ ⊆ protocolCoverage (canonicalRoleAssign cov) P₂ := by
      rw [← protocolCoverage_eq_of_ConsistentWith cov R₂ hR2 P₂]
      exact hC2
    refine ⟨Prot.union P₁ P₂, canonicalRoleAssign cov, ConsistentWith_canonical cov, ?_⟩
    rw [coverage_union]
    exact Finset.union_subset_union hcov1 hcov2
  | subset S C C' _ hsub' ih =>
    obtain ⟨P, R, hR, hC⟩ := ih
    exact ⟨P, R, hR, hsub'.trans hC⟩
  | stratumMono S S' C _ heq ih =>
    subst heq
    exact ih

end CertificationLogic
