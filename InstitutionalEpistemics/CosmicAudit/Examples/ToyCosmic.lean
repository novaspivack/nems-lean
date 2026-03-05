import InstitutionalEpistemics.CosmicAudit.Core.Contexts
import InstitutionalEpistemics.CosmicAudit.Theorems.DiversityLift
import InstitutionalEpistemics.Core.Roles
import InstitutionalEpistemics.Theorems.RobustnessImprovement
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases

/-! Paper 49: Two-context toy (Fin 4); strict improvement and diversity. -/

set_option autoImplicit false

namespace CosmicAudit.Examples

variable (Instance : Type*) [Fintype Instance] [DecidableEq Instance]

/-- Two contexts (n = 2). -/
def toyNumContexts : ℕ := 2

/-- Instance space: four record fragments. -/
def toyInstanceSpace := Fin 4

instance : Fintype (Fin 4) := inferInstance
instance : DecidableEq (Fin 4) := inferInstance

/-- Role 0 covers {0,1}; role 1 covers {2,3}. -/
def toyCov (r : Role 2) : Finset (Fin 4) :=
  match r.idx.val with
  | 0 => {0, 1}
  | _ => {2, 3}

/-- Protocol coverage = union = all four. -/
theorem toy_full_coverage :
    InstitutionalEpistemics.protocolCoverage (Fin 4) 2 toyCov = Finset.univ := by
  ext a
  simp only [InstitutionalEpistemics.protocolCoverage, Finset.mem_biUnion, Finset.mem_univ]
  constructor
  · intro _; trivial
  · intro _
    fin_cases a
    · refine ⟨⟨⟨0, by decide⟩⟩, trivial, ?_⟩; simp only [toyCov]; decide
    · refine ⟨⟨⟨0, by decide⟩⟩, trivial, ?_⟩; simp only [toyCov]; decide
    · refine ⟨⟨⟨1, by decide⟩⟩, trivial, ?_⟩; simp only [toyCov]; decide
    · refine ⟨⟨⟨1, by decide⟩⟩, trivial, ?_⟩; simp only [toyCov]; decide

/-- Strict improvement: each role's cover is a proper subset of protocol coverage. -/
theorem toy_strict_improvement : InstitutionalEpistemics.StrictImprovement (Fin 4) 2 toyCov := by
  intro r
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · simp only [InstitutionalEpistemics.protocolCoverage]
    intro x hx
    rw [Finset.mem_biUnion]
    exact ⟨r, Finset.mem_univ r, hx⟩
  · intro heq
    by_cases h : r.idx.val = 0
    · have h0 : toyCov r = {0, 1} := by unfold toyCov; rw [h]
      rw [h0] at heq
      have h2 : (2 : Fin 4) ∈ InstitutionalEpistemics.protocolCoverage (Fin 4) 2 toyCov := by
        rw [toy_full_coverage]; exact Finset.mem_univ _
      rw [← heq] at h2
      exact absurd h2 (by decide)
    · have hlt : r.idx.val < 2 := r.idx.is_lt
      have hval : r.idx.val = 1 := by omega
      have h1 : toyCov r = {2, 3} := by unfold toyCov; rw [hval]
      rw [h1] at heq
      have h0' : (0 : Fin 4) ∈ InstitutionalEpistemics.protocolCoverage (Fin 4) 2 toyCov := by
        rw [toy_full_coverage]; exact Finset.mem_univ _
      rw [← heq] at h0'
      exact absurd h0' (by decide)

/-- Diversity: two distinct roles with different coverage. -/
theorem toy_diversity :
    Diversity (Fin 4) 2 (fun r => (· ∈ toyCov r)) :=
  diversity_necessary_strict_improvement (Fin 4) 2 toyCov toy_strict_improvement (by omega)

end CosmicAudit.Examples
