import NemS.Prelude
import EpistemicAgency.Core.ClaimDomain
import EpistemicAgency.Core.Protocol
import EpistemicAgency.Theorems.ProtocolStrictImprovement
import EpistemicAgency.Theorems.Diversity

/-!
# EpistemicAgency.Examples.ToySociety

**Toy instance: Fin 4 claim domain, two verifiers with complementary covers (Paper 31).**

Concrete finite witness for strict improvement and diversity necessity.
-/

set_option autoImplicit false

namespace EpistemicAgency

open ClaimDomain

/-- Toy claim domain: four claims with arbitrary truth. -/
def toyTruth (i : Fin 4) : Bool :=
  match i with
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => false
  | ⟨2, _⟩ => true
  | ⟨3, _⟩ => false

def toyDomain : ClaimDomain where
  ClaimId := Fin 4
  Truth := toyTruth
  fintype := inferInstance
  decidableEq := inferInstance

/-- Verifier 1: covers {0,1}, correct on them, abstain elsewhere. -/
def toyV1 : Verifier toyDomain := fun i =>
  match i with
  | ⟨0, _⟩ => Verdict.accept
  | ⟨1, _⟩ => Verdict.reject
  | _ => Verdict.abstain

/-- Verifier 2: covers {2,3}, correct on them, abstain elsewhere. -/
def toyV2 : Verifier toyDomain := fun i =>
  match i with
  | ⟨2, _⟩ => Verdict.accept
  | ⟨3, _⟩ => Verdict.reject
  | _ => Verdict.abstain

def toyC1 : Finset (Fin 4) := {0, 1}
def toyC2 : Finset (Fin 4) := {2, 3}

lemma toySound1 : SoundOnCover toyDomain toyV1 toyC1 := by
  constructor
  · intro c hc
    fin_cases c <;> simp [toyC1] at hc <;> simp [toyV1]
    · rfl
    · rfl
    · cases hc with | inl h | inr h => (have := congr_arg Fin.val h; omega)
    · cases hc with | inl h | inr h => (have := congr_arg Fin.val h; omega)
  · intro c hc
    simp only [toyC1, Finset.mem_insert, Finset.mem_singleton] at hc
    fin_cases c <;> simp only [toyV1]
    · exact (hc (Or.inl rfl)).elim
    · exact (hc (Or.inr rfl)).elim

lemma toySound2 : SoundOnCover toyDomain toyV2 toyC2 := by
  constructor
  · intro c hc
    fin_cases c <;> simp [toyC2] at hc <;> simp [toyV2]
    · rcases hc with h | h
      · have heq := congr_arg Fin.val h; simp at heq
      · have heq := congr_arg Fin.val h; simp at heq
    · rcases hc with h | h
      · have heq := congr_arg Fin.val h; simp at heq
      · have heq := congr_arg Fin.val h; simp at heq
    · rfl
    · rfl
  · intro c hc
    simp only [toyC2, Finset.mem_insert, Finset.mem_singleton] at hc
    fin_cases c <;> simp [toyV2]
    · exact hc (Or.inl (rfl : (⟨2, by omega⟩ : Fin 4) = (2 : Fin 4)))
    · exact hc (Or.inr (rfl : (⟨3, by omega⟩ : Fin 4) = (3 : Fin 4)))

/-- Toy society: two verifiers with complementary covers. -/
def toySociety : Society toyDomain := [(toyV1, toyC1), (toyV2, toyC2)]

lemma toySocietySound : SocietySound toySociety := by
  intro p hp
  simp only [toySociety, List.mem_cons] at hp
  rcases hp with (heq | heq)
  · rw [heq]; exact toySound1
  · rcases heq with (heq2 | ⟨⟩)
    · rw [heq2]; exact toySound2
    · contradiction

/-- Society cover is all four claims. -/
lemma toySocietyCover_full : societyCover toySociety = Finset.univ := by
  ext i
  simp only [societyCover, toySociety, List.foldl_cons, List.foldl_nil, Finset.mem_union,
    toyC1, toyC2, Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ]
  fin_cases i <;> simp

/-- Strict improvement: society covers all claims; each individual covers only two. -/
theorem toy_strict_improvement (i : Fin 4) :
    i ∈ societyCover toySociety ∧ (i ∉ toyC1 ∨ i ∉ toyC2) := by
  rw [toySocietyCover_full]
  simp only [Finset.mem_univ]
  fin_cases i <;> simp [toyC1, toyC2]

/-- Diversity: the two covers are different and incomparable. -/
theorem toy_diversity_necessary : ¬ ∃ C, Homogeneous toySociety C := by
  intro ⟨C, hHom⟩
  have h1 := hHom (toyV1, toyC1) (List.mem_cons.mpr (Or.inl rfl))
  have h2 := hHom (toyV2, toyC2) (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  have : toyC1 = toyC2 := h1.trans h2.symm
  have h0 : (⟨0, by omega⟩ : Fin 4) ∈ toyC1 := Finset.mem_insert_self _ _
  rw [this] at h0
  simp only [toyC2, Finset.mem_insert, Finset.mem_singleton] at h0
  rcases h0 with h | h
  · have heq := congr_arg Fin.val h; simp at heq
  · have heq := congr_arg Fin.val h; simp at heq

end EpistemicAgency
