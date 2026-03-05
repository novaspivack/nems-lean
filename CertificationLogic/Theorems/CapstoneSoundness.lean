import CertificationLogic.Core.Formulas
import CertificationLogic.Core.CertifiableAt
import CertificationLogic.Core.Protocols
import Mathlib.Data.Finset.Basic

/-!
# CertificationLogic.Theorems.CapstoneSoundness — Paper 50 Capstone, T50.1

Soundness: ⊢_S C → CertifiableAt(cov, S, C) for protocol-based semantics.
-/

set_option autoImplicit false

variable (Instance : Type*) [Fintype Instance] [DecidableEq Instance]
variable (n : ℕ) [DecidableEq (InstitutionalEpistemics.Role n)]

namespace CertificationLogic

open CertificationLogic.Protocols

variable {Instance n}

/-- **T50.1 Soundness (capstone):** Every derivable claim set is certifiable. -/
theorem soundness_capstone {Stratum : Type*} (cov : CovMap Instance n) (S : Stratum)
    (C : Formula Instance) (h : Derivable cov (axFromCov cov) S C) :
    CertifiableAt cov S C := by
  induction h with
  | ax S C hax =>
    obtain ⟨r, hC⟩ := hax
    refine ⟨Prot.atom r, canonicalRoleAssign cov, ConsistentWith_canonical cov, ?_⟩
    rw [Protocols.coverage_atom]
    exact hC
  | union S C₁ C₂ _ _ ih1 ih2 =>
    obtain ⟨P₁, R₁, hR1, hC1⟩ := ih1
    obtain ⟨P₂, R₂, hR2, hC2⟩ := ih2
    have hcov1 : C₁ ⊆ Protocols.protocolCoverage (canonicalRoleAssign cov) P₁ :=
      hC1.trans (protocolCoverage_eq_of_ConsistentWith cov R₁ hR1 P₁).ge
    have hcov2 : C₂ ⊆ Protocols.protocolCoverage (canonicalRoleAssign cov) P₂ :=
      hC2.trans (protocolCoverage_eq_of_ConsistentWith cov R₂ hR2 P₂).ge
    refine ⟨Prot.union P₁ P₂, canonicalRoleAssign cov, ConsistentWith_canonical cov, ?_⟩
    rw [Protocols.coverage_union]
    exact Finset.union_subset_union hcov1 hcov2
  | subset S C C' _ hsub hsub' =>
    obtain ⟨P, R, hR, hC⟩ := ih
    exact ⟨P, R, hR, hsub'.trans hC⟩
  | stratumMono S S' C _ heq =>
    rw [heq]; exact ih

end CertificationLogic
