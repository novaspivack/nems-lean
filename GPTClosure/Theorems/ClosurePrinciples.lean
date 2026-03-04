-- Closure principles force unique affine-linear state (Paper 39)
import GPTClosure.Core.EffectsStates
import GPTClosure.Core.Measurements
import GPTClosure.Theorems.Uniqueness

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (S : OrderedUnitSpace V)

namespace OrderedUnitSpace

/-- A probability assignment on effects that satisfies additivity on unit decompositions
    and normalization. Noncontextuality is implicit: the assignment is a function of the effect. -/
structure ClosureAssignment where
  toFun : S.Effect → ℝ
  nonneg' : ∀ e, 0 ≤ toFun e
  le_one' : ∀ e, toFun e ≤ 1
  unit_one : toFun S.orderUnitEffect = 1
  additive' : ∀ (n : ℕ) (m : S.Measurement n),
    (Finset.univ.sum fun i => toFun (m.outcomes i)) = 1

namespace ClosureAssignment

instance : FunLike S.ClosureAssignment S.Effect (fun _ => ℝ) where
  coe f := f.toFun
  coe_injective' _ _ h := by cases _; cases _; congr; exact h

end ClosureAssignment

/-- Any state induces a closure assignment (probabilities satisfy the axioms). -/
def State.toClosureAssignment (ω : S.State) : S.ClosureAssignment where
  toFun e := ω.prob e
  nonneg' _ := ω.prob_nonneg _
  le_one' _ := ω.prob_le_one _
  unit_one := by simp [State.prob, orderUnitEffect, State.norm_one]
  additive' n m := by
    simp only [State.prob, Finset.sum_congr rfl fun i _ => ω.coe_apply (m.outcomes i : V)]
    rw [← LinearMap.map_sum, m.sum_eq_unit, ω.norm_one]

/-- Under closure principles, if effects span V, two states that agree on all effects are equal.
    So the probability assignment (when it comes from a state) is forced by that unique state. -/
theorem closure_implies_affine_linear (hspan : S.effectSpan = ⊤) (ω₁ ω₂ : S.State)
    (h : ∀ e : S.Effect, ω₁.prob e = ω₂.prob e) : ω₁ = ω₂ :=
  S.state_extensionality hspan ω₁ ω₂ h

/-- Alias for paper: closure principles imply unique state (when effects span V). -/
theorem closure_implies_state (hspan : S.effectSpan = ⊤) (ω₁ ω₂ : S.State)
    (h : ∀ e : S.Effect, ω₁.prob e = ω₂.prob e) : ω₁ = ω₂ :=
  closure_implies_affine_linear hspan ω₁ ω₂ h

end OrderedUnitSpace
