import NemS.Quantum.POVM

/-!
# NemS.Quantum.Measures

Probability assignments on quantum effects: normalized, finitely additive
on POVMs. This is the axiomatic setup for the Busch/Gleason theorem.
-/

namespace NemS
namespace Quantum

open BigOperators

/-- A probability assignment on effects with normalization and POVM additivity.
Noncontextuality is automatic (domain is effects, not effect-in-context). -/
structure EffectMeasure (n : ℕ) where
  /-- The probability assignment. -/
  μ : Effect n → ℝ
  /-- Normalization: μ(I) = 1. -/
  normalized : μ Effect.one = 1
  /-- POVM additivity: for any POVM, probabilities sum to 1. -/
  povm_additive : ∀ {k : ℕ} (P : POVM n k), (∑ i, μ (P.effects i)) = 1
  /-- Probabilities are nonneg. -/
  nonneg : ∀ E : Effect n, 0 ≤ μ E
  /-- Probabilities are at most 1. -/
  le_one : ∀ E : Effect n, μ E ≤ 1

namespace EffectMeasure

variable {n : ℕ}

/-- μ(0) = 0, derived from a 2-element POVM {0, I}.
Proof: POVM additivity gives μ(0) + μ(I) = 1, normalization gives μ(I) = 1. -/
theorem μ_zero (m : EffectMeasure n) : m.μ Effect.zero = 0 := by
  -- The POVM {0, I} has effects summing to I
  have hsum : (∑ i : Fin 2, (![Effect.zero, Effect.one] i : Effect n).op) = 1 := by
    simp [Fin.sum_univ_two, Effect.zero, Effect.one]
  let P : POVM n 2 := { effects := ![Effect.zero, Effect.one], sum_eq_one := hsum }
  have hP := m.povm_additive P
  -- Expand the sum over Fin 2
  rw [Fin.sum_univ_two] at hP
  -- hP : m.μ (P.effects 0) + m.μ (P.effects 1) = 1
  -- P.effects 0 = Effect.zero and P.effects 1 = Effect.one
  change m.μ Effect.zero + m.μ Effect.one = 1 at hP
  linarith [m.normalized]

end EffectMeasure

end Quantum
end NemS
