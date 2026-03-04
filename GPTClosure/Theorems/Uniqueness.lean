-- Uniqueness and extensionality of states (Paper 39)
import GPTClosure.Core.EffectsStates
import Mathlib.LinearAlgebra.Span
import Mathlib.LinearAlgebra.FiniteDimensional

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (S : OrderedUnitSpace V)

namespace OrderedUnitSpace

open State Submodule

/-- The subspace of V spanned by effect values. -/
def effectSpan : Submodule ℝ V := span ℝ (Set.range (Subtype.val : S.Effect → V))

/-- States agreeing on all effects are equal when effects span V. -/
theorem state_extensionality (hspan : S.effectSpan = ⊤)
    (ω₁ ω₂ : S.State) (h : ∀ e : S.Effect, ω₁.prob e = ω₂.prob e) : ω₁ = ω₂ := by
  ext v
  have hv : v ∈ S.effectSpan := (eq_top_iff.1 hspan) v
  refine Submodule.span_induction hv ?_ ?_ ?_ ?_
  · rintro x ⟨e, rfl⟩; simp only [State.prob, State.coe_apply]; exact h e
  · simp only [LinearMap.map_zero]
  · intros a b ha hb; simp only [LinearMap.map_add, ha, hb]
  · intros c x hx; simp only [LinearMap.map_smul, hx]

/-- If a set of effects spans V, agreement on that set forces state equality.
    (We state it for the full effect set; for a subset, use span of that subset.) -/
theorem uniqueness_under_spanning (hspan : S.effectSpan = ⊤)
    (ω₁ ω₂ : S.State) (h : ∀ e : S.Effect, ω₁.prob e = ω₂.prob e) : ω₁ = ω₂ :=
  S.state_extensionality hspan ω₁ ω₂ h

end OrderedUnitSpace
