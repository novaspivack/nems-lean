-- Measurements as decompositions of the unit (Paper 39)
import GPTClosure.Core.EffectsStates
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (S : OrderedUnitSpace V)

namespace OrderedUnitSpace

/-- A measurement with n outcomes: finite family of effects summing to the order unit. -/
structure Measurement (n : ℕ) where
  outcomes : Fin n → S.Effect
  sum_eq_unit : (Finset.univ.sum fun i => (outcomes i : V)) = S.orderUnit

end OrderedUnitSpace
