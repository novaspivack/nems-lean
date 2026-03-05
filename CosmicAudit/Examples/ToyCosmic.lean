import InstitutionalEpistemics.CosmicAudit.Core.Contexts
import InstitutionalEpistemics.CosmicAudit.Theorems.DiversityLift
import InstitutionalEpistemics
import InstitutionalEpistemics.Core.Roles
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic

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
def toyCov (r : InstitutionalEpistemics.Core.Roles.Role 2) : Finset (Fin 4) :=
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
    · refine ⟨⟨⟨0, by decide⟩⟩, Finset.mem_univ _, ?_⟩; simp only [toyCov]; trivial
    · refine ⟨⟨⟨0, by decide⟩⟩, Finset.mem_univ _, ?_⟩; simp only [toyCov]; trivial
    · refine ⟨⟨⟨1, by decide⟩⟩, Finset.mem_univ _, ?_⟩; simp only [toyCov]; trivial
    · refine ⟨⟨⟨1, by decide⟩⟩, Finset.mem_univ _, ?_⟩; simp only [toyCov]; trivial

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
    have h0 : (toyCov ⟨⟨0, by decide⟩⟩) = {0, 1} := rfl
    have h1 : (toyCov ⟨⟨1, by decide⟩⟩) = {2, 3} := rfl
    fin_cases r
    · rw [h0] at heq
      have : (2 : Fin 4) ∈ InstitutionalEpistemics.protocolCoverage (Fin 4) 2 toyCov := by
        rw [toy_full_coverage]; exact Finset.mem_univ _
      rw [heq] at this
      simp [toyCov] at this
    · rw [h1] at heq
      have : (0 : Fin 4) ∈ InstitutionalEpistemics.protocolCoverage (Fin 4) 2 toyCov := by
        rw [toy_full_coverage]; exact Finset.mem_univ _
      rw [heq] at this
      simp [toyCov] at this

/-- Diversity: two distinct roles with different coverage. -/
theorem toy_diversity :
    InstitutionalEpistemics.Core.Roles.Diversity (Fin 4) 2 (fun r => (· ∈ toyCov r)) :=
  diversity_necessary_strict_improvement (Fin 4) 2 toyCov toy_strict_improvement (by omega)

end CosmicAudit.Examples
