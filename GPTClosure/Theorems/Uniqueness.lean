-- Uniqueness and extensionality of states (Paper 39)
import GPTClosure.Core.EffectsStates
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (S : OrderedUnitSpace V)

namespace OrderedUnitSpace

open Submodule

/-- The subspace of V spanned by effect values. -/
def effectSpan : Submodule ℝ V := span ℝ (Set.range (Subtype.val : S.Effect → V))

/-- States agreeing on all effects are equal when effects span V. -/
theorem state_ext_effect_span (hspan : S.effectSpan = ⊤)
    (ω₁ ω₂ : S.State) (h : ∀ e : S.Effect, ω₁.toFun e.val = ω₂.toFun e.val) : ω₁ = ω₂ := by
  apply OrderedUnitSpace.State.ext S
  ext v
  have hv : v ∈ S.effectSpan := by rw [hspan]; simp only [Submodule.mem_top]
  induction hv using Submodule.span_induction with
  | mem x hx => rcases hx with ⟨e, rfl⟩; exact h e
  | zero => simp only [LinearMap.map_zero]
  | add x y _ _ hx hy => simp only [LinearMap.map_add, hx, hy]
  | smul c x _ hx => simp only [LinearMap.map_smul, hx]

/-- If a set of effects spans V, agreement on that set forces state equality.
    (We state it for the full effect set; for a subset, use span of that subset.) -/
theorem uniqueness_under_spanning (hspan : S.effectSpan = ⊤)
    (ω₁ ω₂ : S.State) (h : ∀ e : S.Effect, ω₁.toFun e.val = ω₂.toFun e.val) : ω₁ = ω₂ :=
  OrderedUnitSpace.state_ext_effect_span S hspan ω₁ ω₂ h

end OrderedUnitSpace
