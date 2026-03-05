-- Diversity necessity for strict improvement (Paper 40)
import InstitutionalEpistemics.Core.Roles
import InstitutionalEpistemics.Core.ThreatModel
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union

variable (Instance : Type*) [Fintype Instance] [DecidableEq Instance] (n : ℕ) [DecidableEq (Role n)]

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
  set r0 : Role n := ⟨⟨0, by omega⟩⟩ with _; have hr0 := h r0
  obtain ⟨a, ha_in, ha_out⟩ := Finset.exists_of_ssubset hr0
  rw [protocolCoverage, Finset.mem_biUnion] at ha_in
  obtain ⟨s, _, has⟩ := ha_in
  have hne_s : s ≠ r0 := fun heq => ha_out (heq ▸ has)
  refine ⟨s, r0, hne_s, fun heq => ha_out ((heq a).mp has)⟩
