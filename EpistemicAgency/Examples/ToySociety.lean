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

private lemma mem_toyC1 (c : Fin 4) : c ∈ toyC1 ↔ c.val = 0 ∨ c.val = 1 := by
  fin_cases c <;> simp [toyC1, Finset.mem_insert, Finset.mem_singleton]

private lemma mem_toyC2 (c : Fin 4) : c ∈ toyC2 ↔ c.val = 2 ∨ c.val = 3 := by
  fin_cases c <;> simp [toyC2, Finset.mem_insert, Finset.mem_singleton]

lemma toySound1 : SoundOnCover toyDomain toyV1 toyC1 := by
  constructor
  · intro c hc
    match c with
    | ⟨0, _⟩ => simp [toyC1, Finset.mem_insert, Finset.mem_singleton, toyV1, toyTruth] at hc ⊢; rfl
    | ⟨1, _⟩ => simp [toyC1, Finset.mem_insert, Finset.mem_singleton, toyV1, toyTruth] at hc ⊢; rfl
    | ⟨2, _⟩ => simp [toyC1, Finset.mem_insert, Finset.mem_singleton] at hc
    | ⟨3, _⟩ => simp [toyC1, Finset.mem_insert, Finset.mem_singleton] at hc
  · intro c hc
    match c with
    | ⟨0, _⟩ => exfalso; simp [mem_toyC1] at hc
    | ⟨1, _⟩ => exfalso; simp [mem_toyC1] at hc
    | ⟨2, _⟩ => simp [mem_toyC1, toyV1] at hc ⊢; rfl
    | ⟨3, _⟩ => simp [mem_toyC1, toyV1] at hc ⊢; rfl

lemma toySound2 : SoundOnCover toyDomain toyV2 toyC2 := by
  constructor
  · intro c hc
    match c with
    | ⟨0, _⟩ => simp [toyC2, Finset.mem_insert, Finset.mem_singleton] at hc
    | ⟨1, _⟩ => simp [toyC2, Finset.mem_insert, Finset.mem_singleton] at hc
    | ⟨2, _⟩ => simp [toyC2, Finset.mem_insert, Finset.mem_singleton, toyV2, toyTruth] at hc ⊢; rfl
    | ⟨3, _⟩ => simp [toyC2, Finset.mem_insert, Finset.mem_singleton, toyV2, toyTruth] at hc ⊢; rfl
  · intro c hc
    match c with
    | ⟨0, _⟩ => simp [mem_toyC2, toyV2] at hc ⊢; rfl
    | ⟨1, _⟩ => simp [mem_toyC2, toyV2] at hc ⊢; rfl
    | ⟨2, _⟩ => exfalso; simp [toyC2, Finset.mem_insert, Finset.mem_singleton] at hc
    | ⟨3, _⟩ => exfalso; simp [toyC2, Finset.mem_insert, Finset.mem_singleton] at hc

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
  rw [mem_societyCover_iff]
  fin_cases i
  · exact ⟨⟨toyV1, toyC1⟩, List.mem_cons.mpr (Or.inl rfl),
      by simp [toyC1, Finset.mem_insert, Finset.mem_singleton]⟩
  · exact ⟨⟨toyV1, toyC1⟩, List.mem_cons.mpr (Or.inl rfl),
      by simp [toyC1, Finset.mem_insert, Finset.mem_singleton]⟩
  · exact ⟨⟨toyV2, toyC2⟩, List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))),
      by simp [toyC2, Finset.mem_insert, Finset.mem_singleton]⟩
  · exact ⟨⟨toyV2, toyC2⟩, List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))),
      by simp [toyC2, Finset.mem_insert, Finset.mem_singleton]⟩

/-- Strict improvement: society covers all claims; each individual covers only two. -/
theorem toy_strict_improvement (i : Fin 4) :
    i ∈ societyCover toySociety ∧ (i ∉ toyC1 ∨ i ∉ toyC2) := by
  fin_cases i
  · exact ⟨by
      rw [mem_societyCover_iff]
      exact ⟨⟨toyV1, toyC1⟩, List.mem_cons.mpr (Or.inl rfl),
        by simp [toyC1, Finset.mem_insert, Finset.mem_singleton]⟩, by
      right; simp [mem_toyC2]⟩
  · exact ⟨by
      rw [mem_societyCover_iff]
      exact ⟨⟨toyV1, toyC1⟩, List.mem_cons.mpr (Or.inl rfl),
        by simp [toyC1, Finset.mem_insert, Finset.mem_singleton]⟩, by
      right; simp [mem_toyC2]⟩
  · exact ⟨by
      rw [mem_societyCover_iff]
      exact ⟨⟨toyV2, toyC2⟩, List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))),
        by simp [toyC2, Finset.mem_insert, Finset.mem_singleton]⟩, by
      left; simp [mem_toyC1]⟩
  · exact ⟨by
      rw [mem_societyCover_iff]
      exact ⟨⟨toyV2, toyC2⟩, List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))),
        by simp [toyC2, Finset.mem_insert, Finset.mem_singleton]⟩, by
      left; simp [mem_toyC1]⟩

/-- Diversity: the two covers are different and incomparable. -/
theorem toy_diversity_necessary : ¬ ∃ C, Homogeneous toySociety C := by
  intro ⟨C, hHom⟩
  have h1 := hHom (toyV1, toyC1) (List.mem_cons.mpr (Or.inl rfl))
  have h2 := hHom (toyV2, toyC2) (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  have : toyC1 = toyC2 := h1.trans h2.symm
  have h0 : (0 : Fin 4) ∈ toyC1 := Finset.mem_insert_self _ _
  rw [this] at h0
  rw [mem_toyC2] at h0
  simp at h0

end EpistemicAgency
