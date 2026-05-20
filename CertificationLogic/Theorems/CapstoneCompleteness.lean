import CertificationLogic.Core.Formulas
import CertificationLogic.Core.CertifiableAt
import CertificationLogic.Core.Protocols
import Mathlib.Data.Finset.Basic

/-!
# CertificationLogic.Theorems.CapstoneCompleteness — Paper 50 Capstone, T50.2

Completeness: ProtocolCertifiableAt(cov, S, C) → ⊢_S C via protocol normal form.

**Nontriviality:** The proof calculus (⊢_S) does not mention protocols directly. Completeness
requires a **normal-form theorem**: every semantic witness (protocol P with consistent R) can be
turned into a derivation. We do this by structural recursion on P: `derivable_coverage` shows
that the coverage of any protocol is derivable (atoms → Ax, union → Union, inter/prefer →
Subset of the union of branches). Thus completeness is a theorem, not a definition.
-/

set_option autoImplicit false

namespace CertificationLogic

variable {Instance : Type*} [Fintype Instance] [DecidableEq Instance]
variable {n : ℕ} [DecidableEq (Role n)]

/-- Protocol coverage sets are derivable (structural recursion on P; the "normal form" content). -/
theorem derivable_coverage {Stratum : Type*} (cov : Role n → Finset Instance) (S : Stratum)
    (P : Prot n) (R : Role n → Verifier Instance) (hR : ConsistentWith cov R) :
    ProtocolDerivable cov (axFromCov cov) S (protocolCoverage R P) := by
  induction P with
  | atom r =>
    rw [coverage_atom, hR r]
    exact ProtocolDerivable.ax S (cov r) ⟨r, Finset.Subset.refl _⟩
  | union P Q hP hQ =>
    rw [coverage_union]
    exact ProtocolDerivable.union S _ _ hP hQ
  | inter P Q hP hQ =>
    have hsub := protocolCoverage_inter_subset_union R P Q
    exact ProtocolDerivable.subset S (protocolCoverage R P ∪ protocolCoverage R Q)
      (protocolCoverage R (Prot.inter P Q)) (ProtocolDerivable.union S _ _ hP hQ) hsub
  | prefer P Q hP hQ =>
    have hsub := protocolCoverage_prefer_subset_union R P Q
    exact ProtocolDerivable.subset S (protocolCoverage R P ∪ protocolCoverage R Q)
      (protocolCoverage R (Prot.prefer P Q)) (ProtocolDerivable.union S _ _ hP hQ) hsub

/-- **T50.2 Completeness (capstone):** Every certifiable claim set is derivable. -/
theorem completeness_capstone {Stratum : Type*} (cov : Role n → Finset Instance) (S : Stratum)
    (C : Finset Instance) (h : ProtocolCertifiableAt cov S C) :
    ProtocolDerivable cov (axFromCov cov) S C := by
  obtain ⟨P, R, hR, hC⟩ := h
  exact ProtocolDerivable.subset S (protocolCoverage R P) C (derivable_coverage cov S P R hR) hC

end CertificationLogic
