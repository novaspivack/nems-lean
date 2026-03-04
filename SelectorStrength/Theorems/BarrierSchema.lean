import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider

/-!
# SelectorStrength.Theorems.BarrierSchema

**No total decider at strength S (Paper 29 headline).**

If T is extensional and nontrivial, the decider class Sbool and transformer class Sα
are anti-decider closed, and the system has the fixed-point principle for all F in Sα
(hFP : ∀ F, Sα F → ∃ d, Equiv d (F d)), then there is no total decider for T in Sbool.
-/

set_option autoImplicit false

namespace SelectorStrength

universe u

variable {α : Type u}

variable (Equiv : α → α → Prop)

/-- **Barrier schema**: under anti-decider closure and fixed-point principle at strength Sα,
no total decider in Sbool exists for any extensional nontrivial predicate T. -/
theorem no_total_decider_at_strength
    (T : α → Prop)
    (hExt : Extensional Equiv T)
    (true_term : α) (hTrue : T true_term)
    (false_term : α) (hFalse : ¬ T false_term)
    (Sbool : Strength α Bool) (Sα : Strength α α)
    (hAnti : AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : α → α, Sα F → ∃ d : α, Equiv d (F d)) :
    ¬ DecidableAt Sbool T := by
  intro ⟨δ, hSδ, hDec⟩
  -- F = antiDecider δ true_term false_term: when δ x then false_term else true_term
  let F : α → α := antiDecider δ true_term false_term
  have hF_in_Sα : Sα F := hAnti δ hSδ true_term false_term
  obtain ⟨d, hd⟩ := hFP F hF_in_Sα
  have hTd_iff : T d ↔ T (F d) := hExt hd
  simp only [F, antiDecider] at hTd_iff
  by_cases hδ : δ d = true
  · -- δ d = true, so F d = false_term; T d ↔ T false_term; T d from hDec
    simp only [hδ] at hTd_iff
    exact hFalse (hTd_iff.mp ((hDec d).mp hδ))
  · -- ¬(δ d = true), so F d = true_term; T d ↔ T true_term; then T d gives δ d = true, contradiction
    simp only [if_neg hδ] at hTd_iff
    have hTd : T d := hTd_iff.mpr hTrue
    exact absurd ((hDec d).mpr hTd) hδ

/-- **Corollary**: Nontriviality stated as ∃ witnesses. -/
theorem no_total_decider_at_strength_nontrivial
    (T : α → Prop)
    (hExt : Extensional Equiv T)
    (hNontriv : Nontrivial T)
    (Sbool : Strength α Bool) (Sα : Strength α α)
    (hAnti : AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : α → α, Sα F → ∃ d : α, Equiv d (F d)) :
    ¬ DecidableAt Sbool T := by
  obtain ⟨⟨true_term, hTrue⟩, ⟨false_term, hFalse⟩⟩ := hNontriv
  exact no_total_decider_at_strength Equiv T hExt true_term hTrue false_term hFalse
    Sbool Sα hAnti hFP

end SelectorStrength
