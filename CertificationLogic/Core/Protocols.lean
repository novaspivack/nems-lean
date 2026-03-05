import CertificationLogic.Core.InstanceSemantics
import InstitutionalEpistemics.Core.Roles
import Mathlib.Data.Finset.Basic

/-!
# CertificationLogic.Core.Protocols — Paper 50 Capstone

Protocol terms: atom (role), union, inter, prefer.
eval, AdmissibleProt, and coverage semantics.
-/

set_option autoImplicit false

namespace CertificationLogic

variable (Instance : Type*) [Fintype Instance] [DecidableEq Instance]
variable (n : ℕ) [DecidableEq (InstitutionalEpistemics.Role n)]

/-- Protocol term: atoms (roles) and combinators. -/
inductive Prot (n : ℕ)
  | atom (r : InstitutionalEpistemics.Role n)
  | union (P Q : Prot n)
  | inter (P Q : Prot n)
  | prefer (P Q : Prot n)

variable {Instance n}

/-- The set of role atoms that appear in a protocol (for normal-form reasoning). -/
def atoms (P : Prot n) : Finset (InstitutionalEpistemics.Role n) :=
  match P with
  | Prot.atom r => {r}
  | Prot.union P Q => atoms P ∪ atoms Q
  | Prot.inter P Q => atoms P ∪ atoms Q
  | Prot.prefer P Q => atoms P ∪ atoms Q
  end

/-- Role assignment: each role has a verifier. -/
def RoleAssign : Type _ := InstitutionalEpistemics.Role n → CertificationLogic.Verifier Instance

/-- Evaluate protocol to a verifier. -/
def eval (P : Prot n) (R : RoleAssign) : CertificationLogic.Verifier Instance :=
  match P with
  | Prot.atom r => R r
  | Prot.union P Q =>
    fun x => match (eval P R x, eval Q R x) with
      | (CertificationLogic.Verdict.accept, _) | (_, CertificationLogic.Verdict.accept) =>
          CertificationLogic.Verdict.accept
      | (CertificationLogic.Verdict.reject, _) | (_, CertificationLogic.Verdict.reject) =>
          CertificationLogic.Verdict.reject
      | (CertificationLogic.Verdict.abstain, CertificationLogic.Verdict.abstain) =>
          CertificationLogic.Verdict.abstain
  | Prot.inter P Q =>
    fun x => match (eval P R x, eval Q R x) with
      | (CertificationLogic.Verdict.accept, CertificationLogic.Verdict.accept) =>
          CertificationLogic.Verdict.accept
      | (CertificationLogic.Verdict.reject, _) | (_, CertificationLogic.Verdict.reject) =>
          CertificationLogic.Verdict.reject
      | _ => CertificationLogic.Verdict.abstain
  | Prot.prefer P Q =>
    fun x => match (eval P R x, eval Q R x) with
      | (CertificationLogic.Verdict.accept, _) | (CertificationLogic.Verdict.reject, _) => eval P R x
      | (CertificationLogic.Verdict.abstain, v) => v

/-- Coverage of evaluated protocol. -/
def protocolCoverage (R : RoleAssign) (P : Prot n) : Finset Instance :=
  CertificationLogic.coverage (eval P R)

/-- Atomic protocol coverage equals the verifier's non-abstain set. -/
theorem coverage_atom (R : RoleAssign) (r : InstitutionalEpistemics.Role n) :
    protocolCoverage R (Prot.atom r) = CertificationLogic.coverage (R r) := rfl

/-- Union coverage: instances where either branch is non-abstain. -/
theorem coverage_union (R : RoleAssign) (P Q : Prot n) :
    protocolCoverage R (Prot.union P Q) =
    protocolCoverage R P ∪ protocolCoverage R Q := by
  ext x
  simp only [protocolCoverage, CertificationLogic.coverage, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_cases he : eval P R x = CertificationLogic.Verdict.abstain
    · right
      simp only [CertificationLogic.coverage]
      intro heq
      have : eval (Prot.union P Q) R x = CertificationLogic.Verdict.abstain := by
        simp only [eval]
        split_ifs with h1 h2
        · exact heq
        · omega
        · rfl
      exact h this
    · left
      simp only [CertificationLogic.coverage]
      exact he
  · intro h
    simp only [CertificationLogic.coverage]
    cases h with
    | inl hp => exact fun heq => hp (by rw [← heq])
    | inr hq => exact fun heq => hq (by rw [← heq])

/-- For union, coverage includes both constituents. -/
theorem coverage_union_left (R : RoleAssign) (P Q : Prot n) :
    protocolCoverage R P ⊆ protocolCoverage R (Prot.union P Q) := by
  rw [coverage_union]; exact Finset.subset_union_left (protocolCoverage R P) _

theorem coverage_union_right (R : RoleAssign) (P Q : Prot n) :
    protocolCoverage R Q ⊆ protocolCoverage R (Prot.union P Q) := by
  rw [coverage_union]; exact Finset.subset_union_right _ (protocolCoverage R Q)

/-- When R and R' have the same coverage per role, protocol coverage is equal. -/
theorem protocolCoverage_eq_of_same_coverage (R R' : RoleAssign)
    (h : ∀ r, CertificationLogic.coverage (R r) = CertificationLogic.coverage (R' r))
    (P : Prot n) :
    protocolCoverage R P = protocolCoverage R' P := by
  ext x
  simp only [protocolCoverage, CertificationLogic.coverage, Finset.mem_filter,
    Finset.mem_univ, true_and]
  induction P with
  | atom r =>
    rw [CertificationLogic.mem_coverage, CertificationLogic.mem_coverage]
    congr 2
    exact h r
  | union P Q hP hQ =>
    simp only [eval]
    constructor <;> intro hx
    · by_cases heP : eval P R x = CertificationLogic.Verdict.abstain
      · right; rw [← hQ]; exact fun heq => hx (by simp only [eval]; split_ifs <;> simp [heq])
      · left; rw [← hP]; exact heP
    · by_cases heP : eval P R' x = CertificationLogic.Verdict.abstain
      · right; rw [hQ]; exact fun heq => hx (by simp only [eval]; split_ifs <;> simp [heq])
      · left; rw [hP]; exact heP
  | inter P Q hP hQ =>
    simp only [eval]
    split_ifs with h1 h2 h3 h4 h5 h6 <;> try exact Iff.intro (fun _ => trivial) (fun _ => trivial)
    · have := hP; have := hQ; tauto
    · have := hP; have := hQ; tauto
    · have := hP; have := hQ; tauto
  | prefer P Q hP hQ =>
    simp only [eval]
    split_ifs with h1 h2 <;> try exact Iff.intro (fun _ => trivial) (fun _ => trivial)
    · exact hP
    · exact hQ

/-- Inter coverage is contained in the union of the two branches. -/
theorem protocolCoverage_inter_subset_union (R : RoleAssign) (P Q : Prot n) :
    protocolCoverage R (Prot.inter P Q) ⊆ protocolCoverage R P ∪ protocolCoverage R Q := by
  intro x hx
  simp only [protocolCoverage, CertificationLogic.coverage, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  by_cases heP : eval P R x = CertificationLogic.Verdict.abstain
  · right; intro heq; simp only [eval] at hx; split_ifs at hx <;> simp [heq] at hx
  · left; exact heP

/-- Prefer coverage is contained in the union of the two branches. -/
theorem protocolCoverage_prefer_subset_union (R : RoleAssign) (P Q : Prot n) :
    protocolCoverage R (Prot.prefer P Q) ⊆ protocolCoverage R P ∪ protocolCoverage R Q := by
  intro x hx
  simp only [protocolCoverage, CertificationLogic.coverage, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  by_cases heP : eval P R x = CertificationLogic.Verdict.abstain
  · right; intro heq; simp only [eval] at hx; split_ifs at hx <;> simp [heq] at hx
  · left; exact heP

/-- **Normal form (coverage as union of atoms):** For any protocol P and role assignment R,
  the coverage of P is contained in the union of coverages of the roles that appear in P.
  Completeness uses this: every protocol witness normalizes to a derivation built from
  Ax (per atom), Union, and Subset (inter/prefer do not increase coverage beyond that). -/
theorem protocolCoverage_subset_union_atoms (R : RoleAssign) (P : Prot n) :
    protocolCoverage R P ⊆ (atoms P).biUnion (fun r => CertificationLogic.coverage (R r)) := by
  induction P with
  | atom r =>
    simp only [atoms, protocolCoverage, coverage_atom, Finset.biUnion_singleton]
    exact Finset.Subset.refl _
  | union P Q hP hQ =>
    rw [coverage_union, atoms]
    exact Finset.union_subset_union hP hQ
  | inter P Q hP hQ =>
    rw [atoms]
    have hsub := protocolCoverage_inter_subset_union R P Q
    trans protocolCoverage R P ∪ protocolCoverage R Q
    · exact hsub
    · exact Finset.union_subset_union hP hQ
  | prefer P Q hP hQ =>
    rw [atoms]
    have hsub := protocolCoverage_prefer_subset_union R P Q
    trans protocolCoverage R P ∪ protocolCoverage R Q
    · exact hsub
    · exact Finset.union_subset_union hP hQ

end CertificationLogic
