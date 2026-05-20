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

private lemma mem_toyC1_zero : (0 : Fin 4) ∈ toyC1 := by
  simp [toyC1, Finset.mem_insert, Finset.mem_singleton]

private lemma mem_toyC1_one : (1 : Fin 4) ∈ toyC1 := by
  simp [toyC1, Finset.mem_insert, Finset.mem_singleton]

private lemma not_mem_toyC1_of_two (h : Fin 4) (hh : h.val = 2) : h ∉ toyC1 := by
  intro hc; rw [mem_toyC1] at hc; simp [hh] at hc

private lemma not_mem_toyC1_of_three (h : Fin 4) (hh : h.val = 3) : h ∉ toyC1 := by
  intro hc; rw [mem_toyC1] at hc; simp [hh] at hc

private lemma not_mem_toyC2_of_zero (h : Fin 4) (hh : h.val = 0) : h ∉ toyC2 := by
  intro hc; rw [mem_toyC2] at hc; simp [hh] at hc

private lemma not_mem_toyC2_of_one (h : Fin 4) (hh : h.val = 1) : h ∉ toyC2 := by
  intro hc; rw [mem_toyC2] at hc; simp [hh] at hc

lemma toySound1 : SoundOnCover toyDomain toyV1 toyC1 := by
  constructor
  · intro c hc
    match c with
    | ⟨0, h0⟩ => simp [toyC1, Finset.mem_insert, Finset.mem_singleton, toyV1, toyTruth] at hc ⊢; rfl
    | ⟨1, h1⟩ => simp [toyC1, Finset.mem_insert, Finset.mem_singleton, toyV1, toyTruth] at hc ⊢; rfl
    | ⟨2, h2⟩ => exact absurd hc (not_mem_toyC1_of_two ⟨2, h2⟩ rfl)
    | ⟨3, h3⟩ => exact absurd hc (not_mem_toyC1_of_three ⟨3, h3⟩ rfl)
  · intro c hnot
    match c with
    | ⟨0, h0⟩ => exfalso; exact hnot (by simpa using mem_toyC1_zero)
    | ⟨1, h1⟩ => exfalso; exact hnot (by simpa using mem_toyC1_one)
    | ⟨2, _⟩ => simp [mem_toyC1, toyV1]
    | ⟨3, _⟩ => simp [mem_toyC1, toyV1]

lemma toySound2 : SoundOnCover toyDomain toyV2 toyC2 := by
  constructor
  · intro c hc
    match c with
    | ⟨0, h0⟩ => exact absurd hc (not_mem_toyC2_of_zero ⟨0, h0⟩ rfl)
    | ⟨1, h1⟩ => exact absurd hc (not_mem_toyC2_of_one ⟨1, h1⟩ rfl)
    | ⟨2, h2⟩ => simp [toyC2, Finset.mem_insert, Finset.mem_singleton, toyV2, toyTruth] at hc ⊢; rfl
    | ⟨3, h3⟩ => simp [toyC2, Finset.mem_insert, Finset.mem_singleton, toyV2, toyTruth] at hc ⊢; rfl
  · intro c hnot
    match c with
    | ⟨0, _⟩ => simp [mem_toyC2, toyV2]
    | ⟨1, _⟩ => simp [mem_toyC2, toyV2]
    | ⟨2, h2⟩ => exfalso; exact hnot ((mem_toyC2 ⟨2, h2⟩).2 (Or.inl rfl))
    | ⟨3, h3⟩ => exfalso; exact hnot ((mem_toyC2 ⟨3, h3⟩).2 (Or.inr rfl))

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

private lemma mem_societyCover_zero : (0 : Fin 4) ∈ societyCover toySociety := by
  apply (mem_societyCover_iff (soc := toySociety) (c := (0 : Fin 4))).2
  exact ⟨⟨toyV1, toyC1⟩, List.mem_cons.mpr (Or.inl rfl), mem_toyC1_zero⟩

private lemma mem_societyCover_one : (1 : Fin 4) ∈ societyCover toySociety := by
  apply (mem_societyCover_iff (soc := toySociety) (c := (1 : Fin 4))).2
  exact ⟨⟨toyV1, toyC1⟩, List.mem_cons.mpr (Or.inl rfl), mem_toyC1_one⟩

private lemma mem_societyCover_two : (2 : Fin 4) ∈ societyCover toySociety := by
  apply (mem_societyCover_iff (soc := toySociety) (c := (2 : Fin 4))).2
  exact ⟨⟨toyV2, toyC2⟩, List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))),
    show (2 : Fin 4) ∈ toyC2 from by decide⟩

private lemma mem_societyCover_three : (3 : Fin 4) ∈ societyCover toySociety := by
  apply (mem_societyCover_iff (soc := toySociety) (c := (3 : Fin 4))).2
  exact ⟨⟨toyV2, toyC2⟩, List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))),
    show (3 : Fin 4) ∈ toyC2 from by decide⟩

/-- Society cover is all four claims. -/
lemma toySocietyCover_full : societyCover toySociety = Finset.univ := by
  ext i
  simp only [Finset.mem_univ, mem_societyCover_iff, iff_true]
  fin_cases i
  · exact ⟨⟨toyV1, toyC1⟩, List.mem_cons.mpr (Or.inl rfl), mem_toyC1_zero⟩
  · exact ⟨⟨toyV1, toyC1⟩, List.mem_cons.mpr (Or.inl rfl), mem_toyC1_one⟩
  · exact ⟨⟨toyV2, toyC2⟩, List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))),
      show (2 : Fin 4) ∈ toyC2 from by decide⟩
  · exact ⟨⟨toyV2, toyC2⟩, List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))),
      show (3 : Fin 4) ∈ toyC2 from by decide⟩

/-- Strict improvement: society covers all claims; each individual covers only two. -/
theorem toy_strict_improvement (i : Fin 4) :
    i ∈ societyCover toySociety ∧ (i ∉ toyC1 ∨ i ∉ toyC2) := by
  fin_cases i
  · exact ⟨mem_societyCover_zero, by right; simp [mem_toyC2]⟩
  · exact ⟨mem_societyCover_one, by right; simp [mem_toyC2]⟩
  · exact ⟨mem_societyCover_two, by left; simp [mem_toyC1]⟩
  · exact ⟨mem_societyCover_three, by left; simp [mem_toyC1]⟩

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
