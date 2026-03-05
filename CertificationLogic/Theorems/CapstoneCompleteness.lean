import CertificationLogic.Core.Formulas
import CertificationLogic.Core.CertifiableAt
import CertificationLogic.Core.Protocols
import Mathlib.Data.Finset.Basic

/-!
# CertificationLogic.Theorems.CapstoneCompleteness — Paper 50 Capstone, T50.2

Completeness: CertifiableAt(cov, S, C) → ⊢_S C via protocol normal form.

**Nontriviality:** The proof calculus (⊢_S) does not mention protocols directly. Completeness
requires a **normal-form theorem**: every semantic witness (protocol P with consistent R) can be
turned into a derivation. We do this by structural recursion on P: `derivable_coverage` shows
that the coverage of any protocol is derivable (atoms → Ax, union → Union, inter/prefer →
Subset of the union of branches). Thus completeness is a theorem, not a definition.
-/

set_option autoImplicit false

variable (Instance : Type*) [Fintype Instance] [DecidableEq Instance]
variable (n : ℕ) [DecidableEq (InstitutionalEpistemics.Role n)]

namespace CertificationLogic

open CertificationLogic.Protocols

variable {Instance n}

/-- Protocol coverage sets are derivable (structural recursion on P; the "normal form" content). -/
theorem derivable_coverage {Stratum : Type*} (cov : CovMap Instance n) (S : Stratum)
    (P : Protocols.Prot n) (R : Protocols.RoleAssign) (hR : ConsistentWith cov R) :
    Derivable cov (axFromCov cov) S (Protocols.protocolCoverage R P) := by
  induction P with
  | atom r =>
    rw [Protocols.coverage_atom, hR r]
    exact Derivable.ax S (cov r) ⟨r, Finset.Subset.refl _⟩
  | union P Q hP hQ =>
    rw [Protocols.coverage_union]
    exact Derivable.union S _ _ hP hQ
  | inter P Q hP hQ =>
    have hsub := Protocols.protocolCoverage_inter_subset_union R P Q
    exact Derivable.subset S (Protocols.protocolCoverage R P ∪ Protocols.protocolCoverage R Q)
      (Protocols.protocolCoverage R (Prot.inter P Q)) (Derivable.union S _ _ hP hQ) hsub
  | prefer P Q hP hQ =>
    have hsub := Protocols.protocolCoverage_prefer_subset_union R P Q
    exact Derivable.subset S (Protocols.protocolCoverage R P ∪ Protocols.protocolCoverage R Q)
      (Protocols.protocolCoverage R (Prot.prefer P Q)) (Derivable.union S _ _ hP hQ) hsub

/-- **T50.2 Completeness (capstone):** Every certifiable claim set is derivable. -/
theorem completeness_capstone {Stratum : Type*} (cov : CovMap Instance n) (S : Stratum)
    (C : Formula Instance) (h : CertifiableAt cov S C) :
    Derivable cov (axFromCov cov) S C := by
  obtain ⟨P, R, hR, hC⟩ := h
  exact Derivable.subset S (Protocols.protocolCoverage R P) C (derivable_coverage cov S P R hR) hC

end CertificationLogic
