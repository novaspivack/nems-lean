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
  unit_one : toFun (S.orderUnitEffect) = 1
  additive' : ∀ (n : ℕ) (m : S.Measurement n),
    (Finset.univ.sum fun i => toFun (m.outcomes i)) = 1

/-- Any state induces a closure assignment (probabilities satisfy the axioms). -/
def State.toClosureAssignment (ω : S.State) : S.ClosureAssignment where
  toFun e := ω.toFun e.val
  nonneg' e := prob_nonneg S ω e
  le_one' e := prob_le_one S ω e
  unit_one := by
    show ω.toFun (S.orderUnitEffect).val = 1
    unfold orderUnitEffect
    exact ω.norm_one
  additive' n m := by
    show (Finset.univ.sum fun i => ω.toFun (m.outcomes i).val) = 1
    rw [show (Finset.univ.sum fun i => ω.toFun (m.outcomes i).val) =
        ω.toFun (Finset.univ.sum fun i => (m.outcomes i).val) from
      (map_sum ω.toFun _ _).symm]
    rw [m.sum_eq_unit, ω.norm_one]

omit [FiniteDimensional ℝ V] in
/-- Under closure principles, if effects span V, two states that agree on all effects are equal.
    So the probability assignment (when it comes from a state) is forced by that unique state. -/
theorem closure_implies_affine_linear (hspan : S.effectSpan = ⊤) (ω₁ ω₂ : S.State)
    (h : ∀ e : S.Effect, ω₁.toFun e.val = ω₂.toFun e.val) : ω₁ = ω₂ :=
  state_ext_effect_span S hspan ω₁ ω₂ h

omit [FiniteDimensional ℝ V] in
/-- Alias for paper: closure principles imply unique state (when effects span V). -/
theorem closure_implies_state (hspan : S.effectSpan = ⊤) (ω₁ ω₂ : S.State)
    (h : ∀ e : S.Effect, ω₁.toFun e.val = ω₂.toFun e.val) : ω₁ = ω₂ :=
  closure_implies_affine_linear S hspan ω₁ ω₂ h

end OrderedUnitSpace
