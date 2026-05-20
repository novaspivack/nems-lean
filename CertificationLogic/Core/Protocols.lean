import CertificationLogic.Core.InstanceSemantics
import InstitutionalEpistemics.Core.Roles
import Mathlib.Data.Finset.Union

/-!
# CertificationLogic.Core.Protocols — Paper 50 Capstone

Protocol terms: atom (role), union, inter, prefer.
eval, AdmissibleProt, and coverage semantics.
-/

set_option autoImplicit false

namespace CertificationLogic

/-- Protocol term: atoms (roles) and combinators. -/
inductive Prot (n : ℕ)
  | atom (r : Role n)
  | union (P Q : Prot n)
  | inter (P Q : Prot n)
  | prefer (P Q : Prot n)

/-- The set of role atoms that appear in a protocol (for normal-form reasoning). -/
def atoms {n : ℕ} (P : Prot n) : Finset (Role n) :=
  match P with
  | Prot.atom r => {r}
  | Prot.union P Q => atoms P ∪ atoms Q
  | Prot.inter P Q => atoms P ∪ atoms Q
  | Prot.prefer P Q => atoms P ∪ atoms Q

/-- Role assignment: each role has a verifier. -/
abbrev RoleAssign (Instance : Type*) (n : ℕ) : Type _ :=
  Role n → CertificationLogic.Verifier Instance

/-- Evaluate protocol to a verifier. -/
def eval {Instance : Type*} [Fintype Instance] [DecidableEq Instance]
    {n : ℕ} [DecidableEq (Role n)] (P : Prot n)
    (R : Role n → CertificationLogic.Verifier Instance) :
    CertificationLogic.Verifier Instance :=
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
def protocolCoverage {Instance : Type*} [Fintype Instance] [DecidableEq Instance]
    {n : ℕ} [DecidableEq (Role n)]
    (R : Role n → CertificationLogic.Verifier Instance) (P : Prot n) :
    Finset Instance :=
  CertificationLogic.coverage (eval P R)

/-- Atomic protocol coverage equals the verifier's non-abstain set. -/
theorem coverage_atom {Instance : Type*} [Fintype Instance] [DecidableEq Instance]
    {n : ℕ} [DecidableEq (Role n)]
    (R : Role n → CertificationLogic.Verifier Instance) (r : Role n) :
    protocolCoverage R (Prot.atom r) = CertificationLogic.coverage (R r) := rfl

/-- Evaluating a union protocol abstains only when both branches abstain. -/
theorem eval_union_ne_abstain_iff {Instance : Type*} [Fintype Instance] [DecidableEq Instance]
    {n : ℕ} [DecidableEq (Role n)]
    (R : Role n → CertificationLogic.Verifier Instance) (P Q : Prot n) (x : Instance) :
    eval (Prot.union P Q) R x ≠ CertificationLogic.Verdict.abstain ↔
      eval P R x ≠ CertificationLogic.Verdict.abstain ∨
        eval Q R x ≠ CertificationLogic.Verdict.abstain := by
  simp only [eval]
  rcases hp : eval P R x with (_ | _ | _) <;> rcases hq : eval Q R x with (_ | _ | _) <;>
    simp

/-- Union coverage: instances where either branch is non-abstain. -/
theorem coverage_union {Instance : Type*} [Fintype Instance] [DecidableEq Instance]
    {n : ℕ} [DecidableEq (Role n)]
    (R : Role n → CertificationLogic.Verifier Instance) (P Q : Prot n) :
    protocolCoverage R (Prot.union P Q) =
    protocolCoverage R P ∪ protocolCoverage R Q := by
  ext x
  simp [protocolCoverage, CertificationLogic.mem_coverage, Finset.mem_union, eval_union_ne_abstain_iff]

/-- For union, coverage includes both constituents. -/
theorem coverage_union_left {Instance : Type*} [Fintype Instance] [DecidableEq Instance]
    {n : ℕ} [DecidableEq (Role n)]
    (R : Role n → CertificationLogic.Verifier Instance) (P Q : Prot n) :
    protocolCoverage R P ⊆ protocolCoverage R (Prot.union P Q) := by
  intro x hx
  have : x ∈ protocolCoverage R P ∪ protocolCoverage R Q := Or.inl hx
  rwa [← coverage_union, CertificationLogic.mem_coverage]

theorem coverage_union_right {Instance : Type*} [Fintype Instance] [DecidableEq Instance]
    {n : ℕ} [DecidableEq (Role n)]
    (R : Role n → CertificationLogic.Verifier Instance) (P Q : Prot n) :
    protocolCoverage R Q ⊆ protocolCoverage R (Prot.union P Q) := by
  intro x hx
  have : x ∈ protocolCoverage R P ∪ protocolCoverage R Q := Or.inr hx
  rwa [← coverage_union, CertificationLogic.mem_coverage]

/-- When R and R' have the same coverage per role, protocol coverage is equal. -/
theorem protocolCoverage_eq_of_same_coverage {Instance : Type*} [Fintype Instance]
    [DecidableEq Instance] {n : ℕ} [DecidableEq (Role n)]
    (R R' : Role n → CertificationLogic.Verifier Instance)
    (h : ∀ r, CertificationLogic.coverage (R r) = CertificationLogic.coverage (R' r))
    (P : Prot n) :
    protocolCoverage R P = protocolCoverage R' P := by
  induction P with
  | atom r =>
    ext x
    simp [protocolCoverage, coverage_atom, h r, CertificationLogic.mem_coverage]
  | union P Q ihP ihQ =>
    ext x
    rw [ihP, ihQ, coverage_union]
  | inter P Q ihP ihQ =>
    ext x
    by_cases hP : eval P R x = CertificationLogic.Verdict.abstain <;>
      by_cases hQ : eval Q R x = CertificationLogic.Verdict.abstain <;>
      by_cases hP' : eval P R' x = CertificationLogic.Verdict.abstain <;>
      by_cases hQ' : eval Q R' x = CertificationLogic.Verdict.abstain <;>
      simp [protocolCoverage, eval, hP, hQ, hP', hQ', CertificationLogic.mem_coverage, ihP, ihQ]
  | prefer P Q ihP ihQ =>
    ext x
    by_cases hP : eval P R x = CertificationLogic.Verdict.abstain <;>
      by_cases hQ : eval Q R x = CertificationLogic.Verdict.abstain <;>
      by_cases hP' : eval P R' x = CertificationLogic.Verdict.abstain <;>
      by_cases hQ' : eval Q R' x = CertificationLogic.Verdict.abstain <;>
      simp [protocolCoverage, eval, hP, hQ, hP', hQ', CertificationLogic.mem_coverage, ihP, ihQ]

/-- Inter coverage is contained in the union of the two branches. -/
theorem protocolCoverage_inter_subset_union {Instance : Type*} [Fintype Instance]
    [DecidableEq Instance] {n : ℕ} [DecidableEq (Role n)]
    (R : Role n → CertificationLogic.Verifier Instance) (P Q : Prot n) :
    protocolCoverage R (Prot.inter P Q) ⊆ protocolCoverage R P ∪ protocolCoverage R Q := by
  intro x hx
  rw [CertificationLogic.mem_coverage] at hx ⊢
  by_cases hP : eval P R x = CertificationLogic.Verdict.abstain <;>
    by_cases hQ : eval Q R x = CertificationLogic.Verdict.abstain <;>
    simp [protocolCoverage, eval, hP, hQ, CertificationLogic.mem_coverage, Finset.mem_union] at hx ⊢ <;>
    tauto

/-- Prefer coverage is contained in the union of the two branches. -/
theorem protocolCoverage_prefer_subset_union {Instance : Type*} [Fintype Instance]
    [DecidableEq Instance] {n : ℕ} [DecidableEq (Role n)]
    (R : Role n → CertificationLogic.Verifier Instance) (P Q : Prot n) :
    protocolCoverage R (Prot.prefer P Q) ⊆ protocolCoverage R P ∪ protocolCoverage R Q := by
  intro x hx
  rw [CertificationLogic.mem_coverage] at hx ⊢
  by_cases hP : eval P R x = CertificationLogic.Verdict.abstain <;>
    by_cases hQ : eval Q R x = CertificationLogic.Verdict.abstain <;>
    simp [protocolCoverage, eval, hP, hQ, CertificationLogic.mem_coverage, Finset.mem_union] at hx ⊢ <;>
    tauto

/-- **Normal form (coverage as union of atoms):** For any protocol P and role assignment R,
  the coverage of P is contained in the union of coverages of the roles that appear in P.
  Completeness uses this: every protocol witness normalizes to a derivation built from
  Ax (per atom), Union, and Subset (inter/prefer do not increase coverage beyond that). -/
theorem protocolCoverage_subset_union_atoms {Instance : Type*} [Fintype Instance]
    [DecidableEq Instance] {n : ℕ} [DecidableEq (Role n)]
    (R : Role n → CertificationLogic.Verifier Instance) (P : Prot n) :
    protocolCoverage R P ⊆ (atoms P).biUnion (fun r => CertificationLogic.coverage (R r)) := by
  induction P with
  | atom r =>
    intro x hx
    rw [protocolCoverage, coverage_atom, CertificationLogic.mem_coverage] at hx
    rw [CertificationLogic.mem_coverage, atoms, Finset.mem_biUnion, Finset.mem_singleton]
    exact ⟨r, hx, rfl⟩
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
