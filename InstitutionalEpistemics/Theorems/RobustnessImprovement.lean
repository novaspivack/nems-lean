-- Diversity necessity for strict improvement (Paper 40)
import InstitutionalEpistemics.Core.Roles
import InstitutionalEpistemics.Core.ThreatModel
import Mathlib.Data.Finset.Basic

variable (Instance : Type*) [Fintype Instance] (n : ℕ) [DecidableEq (Role n)]

namespace InstitutionalEpistemics

/-- Certified coverage of a protocol (union of coverage sets of roles that participate). -/
def protocolCoverage (cov : Role n → Finset Instance) : Finset Instance :=
  Finset.univ.biUnion (fun r : Role n => cov r)

/-- Strict improvement: coverage strictly larger than that of any single role. -/
def StrictImprovement (cov : Role n → Finset Instance) : Prop :=
  ∀ r : Role n, cov r ⊂ protocolCoverage Instance n cov

/-- Diversity necessity: strict improvement implies at least two non-equivalent roles. -/
theorem diversity_necessity (cov : Role n → Finset Instance) (h : StrictImprovement Instance n cov)
    (hcard : n ≥ 2) : Diversity Instance n (fun r => (· ∈ cov r)) := by
  set r0 := ⟨0, by omega⟩ with _; have hr0 := h r0
  rw [Finset.ssubset_iff_subset_ne] at hr0; obtain ⟨_, hne⟩ := hr0
  have hsub : cov r0 ⊆ protocolCoverage Instance n cov := Finset.subset_biUnion_of_mem (Finset.mem_univ r0)
  obtain ⟨a, ha⟩ := Finset.ne_iff_exists_mem.mp hne
  have key : a ∉ cov r0 ∧ a ∈ protocolCoverage Instance n cov := by
    by_cases ha0 : a ∈ cov r0
    · exfalso; exact ha (propext ⟨fun _ => hsub ha0, fun _ => ha0⟩)
    · by_cases hP : a ∈ protocolCoverage Instance n cov
      · exact ⟨ha0, hP⟩
      · exfalso; exact ha (propext ⟨fun h => (ha0 h).elim, fun h => (hP h).elim⟩)
  obtain ⟨ha_out, ha_in⟩ := key
  rw [protocolCoverage, Finset.mem_biUnion] at ha_in
  obtain ⟨s, _, has⟩ := ha_in
  have hne_s : s ≠ r0 := fun heq => ha_out (heq ▸ has)
  refine ⟨s, r0, hne_s, fun heq => ha_out ((heq a).mp has)⟩
