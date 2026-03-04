import NemS.Prelude
import EpistemicAgency.Core.ClaimDomain
import EpistemicAgency.Core.Protocol

/-!
# EpistemicAgency.Theorems.Diversity

**Diversity necessity and sufficiency (Paper 31).**

Homogeneous societies cannot strictly improve under admissible protocols.
Role diversity (non-identical coverage sets) is necessary and, for two verifiers
with incomparable covers, sufficient for strict improvement.
-/

set_option autoImplicit false

namespace EpistemicAgency

variable {D : ClaimDomain}

open ClaimDomain

/-- **Homogeneous** society: all verifiers have the same coverage set. -/
def Homogeneous (soc : Society D) (C : Finset D.ClaimId) : Prop :=
  ∀ p ∈ soc, p.2 = C

/-- **Homogeneous no-improvement**: for an admissible protocol, the aggregate's
certified coverage is contained in the common cover. So no admissible protocol
can have certified coverage strictly larger than C. -/
theorem homogeneous_no_improvement (soc : Society D) (C : Finset D.ClaimId)
    (hHom : Homogeneous soc C) (hSound : SocietySound soc)
    (Prot : List (Verifier D) → Verifier D) (hAdm : Admissible Prot) :
    ∀ c, (Prot (societyVerifiers soc) c ≠ Verdict.abstain → c ∈ C) := by
  intro c hneq
  by_contra hnc
  have habs : ∀ V ∈ societyVerifiers soc, V c = Verdict.abstain := by
    intro V hV
    simp only [societyVerifiers, List.mem_map] at hV
    obtain ⟨⟨V', C'⟩, hmem, rfl⟩ := hV
    have C'_eq : C' = C := hHom (V', C') hmem
    have sound := hSound (V', C') hmem
    have c_nc' : c ∉ C' := by rw [C'_eq]; exact hnc
    exact sound.2 c c_nc'
  have habs' := hAdm (societyVerifiers soc) c habs
  exact hneq habs'

/-- **Diversity necessary**: if some admissible protocol has certified coverage
strictly larger than every individual's cover, then the society is not homogeneous
(with a single common cover). So there must exist two verifiers with different covers. -/
theorem diversity_necessary (soc : Society D) (hSound : SocietySound soc)
    (Prot : List (Verifier D) → Verifier D) (hAdm : Admissible Prot)
    (hStrict : ∃ c, Prot (societyVerifiers soc) c ≠ Verdict.abstain ∧
      ∀ p ∈ soc, c ∉ p.2)
    (hnonempty : ∃ p, p ∈ soc) :
    ¬ ∃ C, Homogeneous soc C := by
  intro ⟨C, hHom⟩
  obtain ⟨c, hneq, hc⟩ := hStrict
  have c_in_C := homogeneous_no_improvement soc C hHom hSound Prot hAdm c hneq
  obtain ⟨⟨V, C'⟩, hmem⟩ := hnonempty
  have C'_eq : C' = C := hHom (V, C') hmem
  have c_not_in_C' : c ∉ C' := hc (V, C') hmem
  rw [C'_eq] at c_not_in_C'
  exact c_not_in_C' c_in_C

/-- **Diversity sufficient (two roles)**: if there are two verifiers with
incomparable covers (neither contained in the other), then the union protocol
strictly improves both. -/
theorem diversity_strict_improvement (soc : Society D) (_hSound : SocietySound soc)
    (p q : Verifier D × Finset D.ClaimId) (hp : p ∈ soc) (hq : q ∈ soc)
    (h1 : ¬ p.2 ⊆ q.2) (h2 : ¬ q.2 ⊆ p.2) :
    ∃ c ∈ societyCover soc, c ∉ p.2 ∧ ∃ d ∈ societyCover soc, d ∉ q.2 := by
  obtain ⟨c, hc_p, hc_q⟩ : ∃ c, c ∈ p.2 ∧ c ∉ q.2 := Finset.not_subset.mp h1
  obtain ⟨d, hd_q, hd_p⟩ : ∃ d, d ∈ q.2 ∧ d ∉ p.2 := Finset.not_subset.mp h2
  have hc_cover : c ∈ societyCover soc := by
    rw [mem_societyCover_iff]; exact ⟨p, hp, hc_p⟩
  have hd_cover : d ∈ societyCover soc := by
    rw [mem_societyCover_iff]; exact ⟨q, hq, hd_q⟩
  exact ⟨d, hd_cover, ⟨hd_p, ⟨c, hc_cover, hc_q⟩⟩⟩

end EpistemicAgency
