import NemS.Prelude
import EpistemicAgency.Core.ClaimDomain

/-!
# EpistemicAgency.Core.Protocol

**Admissible protocols and union protocol (Paper 31).**

A protocol aggregates a finite collection of verifiers into a society-level verifier.
Admissible protocols do not assert answers when all inputs abstain.
-/

set_option autoImplicit false

namespace EpistemicAgency

variable {D : ClaimDomain}

open ClaimDomain

/-- A **society** is a list of verifier–cover pairs, each sound on its cover. -/
@[reducible]
def Society (D : ClaimDomain) := List (Verifier D × Finset D.ClaimId)

instance (D : ClaimDomain) : Membership (Verifier D × Finset D.ClaimId) (Society D) :=
  inferInstanceAs (Membership (Verifier D × Finset D.ClaimId) (List (Verifier D × Finset D.ClaimId)))

/-- **Union protocol** on a list of verifiers: accept if any accepts,
  else reject if any rejects, else abstain. -/
def unionProtocol (Vs : List (Verifier D)) (c : D.ClaimId) : Verdict :=
  if Vs.any (fun V => decide (V c = Verdict.accept)) then Verdict.accept
  else if Vs.any (fun V => decide (V c = Verdict.reject)) then Verdict.reject
  else Verdict.abstain

/-- **Society cover**: union of all covers in the society. -/
def societyCover (soc : Society D) : Finset D.ClaimId :=
  soc.foldl (fun acc ⟨_, C⟩ => acc ∪ C) ∅

/-- **Admissible** protocol: when all verifiers abstain on `c`, the aggregate abstains. -/
def Admissible (Prot : List (Verifier D) → Verifier D) : Prop :=
  ∀ (Vs : List (Verifier D)) (c : D.ClaimId),
    (∀ V ∈ Vs, V c = Verdict.abstain) → Prot Vs c = Verdict.abstain

/-- The union protocol is admissible. -/
theorem unionProtocol_admissible (D : ClaimDomain) :
    Admissible (fun (Vs : List (Verifier D)) (c : D.ClaimId) => unionProtocol Vs c) := by
  intro Vs c h
  simp only [unionProtocol]
  by_cases hacc : (Vs.any (fun V => decide (V c = Verdict.accept))) = true
  · exfalso
    rw [List.any_eq_true] at hacc
    obtain ⟨V, hV, heq⟩ := hacc
    have := h V hV
    rw [decide_eq_true_iff] at heq
    rw [heq] at this
    simp at this
  · by_cases hrej : (Vs.any (fun V => decide (V c = Verdict.reject))) = true
    · exfalso
      rw [List.any_eq_true] at hrej
      obtain ⟨V, hV, heq⟩ := hrej
      have := h V hV
      rw [decide_eq_true_iff] at heq
      rw [heq] at this
      simp at this
    · simp [hacc, hrej]

/-- Extract the list of verifiers from a society. -/
def societyVerifiers (soc : Society D) : List (Verifier D) :=
  soc.map Prod.fst

/-- Union protocol applied to a society (using its verifiers). -/
def unionProtocolOfSociety (soc : Society D) : Verifier D :=
  fun c => unionProtocol (societyVerifiers soc) c

/-- Society is sound when each (V,C) has SoundOnCover V C. -/
def SocietySound (soc : Society D) : Prop :=
  ∀ p ∈ soc, ClaimDomain.SoundOnCover D p.1 p.2

lemma mem_foldl_union (soc : Society D) (acc : Finset D.ClaimId) (c : D.ClaimId) :
    c ∈ soc.foldl (fun a ⟨_, C⟩ => a ∪ C) acc ↔ c ∈ acc ∨ ∃ p ∈ soc, c ∈ p.2 := by
  induction soc generalizing acc with
  | nil => simp
  | cons a soc ih =>
    simp only [List.foldl_cons]
    rw [ih]
    constructor
    · intro h
      apply Or.elim h
      · intro hc
        rcases Finset.mem_union.1 hc with (hc' | hc')
        · exact Or.inl hc'
        · exact Or.inr ⟨a, List.mem_cons.mpr (Or.inl rfl), hc'⟩
      · intro hor
        right
        obtain ⟨p, hp, hcp⟩ := hor
        exact ⟨p, List.mem_cons.mpr (Or.inr hp), hcp⟩
    · intro h
      rcases h with (hc | hex)
      · left; exact Finset.mem_union_left a.2 hc
      · obtain ⟨r, hr1, hr2⟩ := hex
        rcases List.mem_cons.1 hr1 with (heq | hr1')
        · rw [heq] at hr2; left; exact Finset.mem_union_right acc hr2
        · right; exact ⟨r, hr1', hr2⟩

lemma mem_societyCover_iff (soc : Society D) (c : D.ClaimId) :
    c ∈ societyCover soc ↔ ∃ p ∈ soc, c ∈ p.2 := by
  simp only [societyCover]
  rw [mem_foldl_union]
  simp

/-- Coverage of the union protocol equals the union of covers (membership). -/
theorem coverage_union_protocol (soc : Society D) (h : SocietySound soc) :
    ∀ c, c ∈ societyCover soc ↔ unionProtocolOfSociety soc c ≠ Verdict.abstain := by
  intro c
  rw [mem_societyCover_iff]
  simp only [unionProtocolOfSociety, societyVerifiers, unionProtocol]
  constructor
  · intro ⟨⟨V, C⟩, hmem, hcC⟩
    have sound := h (V, C) hmem
    have onC := sound.1 c hcC
    have vneq : V c ≠ Verdict.abstain := by
      intro habs
      by_cases ht : D.Truth c = true
      · have h1 := Iff.mpr onC.1 ht; simp at h1; rw [h1] at habs; simp at habs
      · have hf : D.Truth c = false := Bool.eq_false_iff.mpr ht
        have h2 := Iff.mpr onC.2 hf; simp at h2; rw [h2] at habs; simp at habs
    by_cases hV : V c = Verdict.accept
    · intro habs
      have : (soc.map Prod.fst).any (fun W => decide (W c = Verdict.accept)) = true := by
        rw [List.any_eq_true]
        refine ⟨V, List.mem_map.mpr ⟨(V, C), hmem, rfl⟩, ?_⟩
        rw [decide_eq_true_iff]; exact hV
      simp [this] at habs
    · have hV' : V c = Verdict.reject := by
        cases hVc : V c with
        | accept => exact (hV hVc).elim
        | reject => rfl
        | abstain => exact (vneq hVc).elim
      by_cases hacc_inner : (soc.map Prod.fst).any (fun W => decide (W c = Verdict.accept)) = true
      · intro habs
        simp only [hacc_inner] at habs
        simp at habs
      · intro habs
        have hrej_eq : (soc.map Prod.fst).any (fun W => decide (W c = Verdict.reject)) = true := by
          rw [List.any_eq_true]
          refine ⟨V, List.mem_map.mpr ⟨(V, C), hmem, rfl⟩, ?_⟩
          rw [decide_eq_true_iff]; exact hV'
        simp only [hacc_inner, hrej_eq] at habs
        exact (by simp at habs)
  · intro hneq
    by_cases hacc : (soc.map Prod.fst).any (fun V => decide (V c = Verdict.accept))
    · rw [List.any_eq_true] at hacc
      obtain ⟨V, hV, heq⟩ := hacc
      rw [decide_eq_true_iff] at heq
      simp only [List.mem_map] at hV
      obtain ⟨⟨V', C⟩, hmem, rfl⟩ := hV
      refine ⟨(V', C), hmem, ?_⟩
      by_contra hnc
      have sound := h (V', C) hmem
      have habs := sound.2 c hnc
      rw [heq] at habs
      simp at habs
    · by_cases hrej : (soc.map Prod.fst).any (fun V => decide (V c = Verdict.reject))
      · rw [List.any_eq_true] at hrej
        obtain ⟨V, hV, heq⟩ := hrej
        rw [decide_eq_true_iff] at heq
        simp only [List.mem_map] at hV
        obtain ⟨⟨V', C⟩, hmem, rfl⟩ := hV
        refine ⟨(V', C), hmem, ?_⟩
        by_contra hnc
        have sound := h (V', C) hmem
        have := sound.2 c hnc
        rw [heq] at this
        simp at this
      · simp only [hacc, hrej] at hneq
        exfalso
        exact hneq rfl

end EpistemicAgency
