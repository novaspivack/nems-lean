-- Classical simplex: V = Fin n → ℝ, coordinatewise cone, u = 1 (Paper 39)
import GPTClosure.Core.OrderedSpaces
import GPTClosure.Core.EffectsStates
import GPTClosure.Core.Measurements
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Finsupp

variable (n : ℕ) [NeZero n]

namespace GPTClosure.Examples.Toy

-- V = Fin n → ℝ (classical simplex); cone = coordinatewise nonnegative
def ToyCone : ConePredicate (Fin n → ℝ) where
  Pos f := ∀ i, 0 ≤ f i
  pos_zero _ := by simp
  pos_add _ _ hf hg i := by simp; exact add_nonneg (hf i) (hg i)
  pos_smul c _ hc hf i := by simp; exact mul_nonneg hc (hf i)
  pos_neg_iff_zero f hf hneg := by ext i; linarith [hf i, hneg i]

def toyOrderUnit : Fin n → ℝ := fun _ => 1

def ToySpace : OrderedUnitSpace (Fin n → ℝ) where
  cone := ToyCone
  orderUnit := toyOrderUnit
  pos_order_unit _ := zero_le_one

/-- Standard basis vector as effect (single outcome i with probability 1 at that slot). -/
def effectAt (i : Fin n) : ToySpace.Effect := ⟨fun j => if j = i then 1 else 0, by
  constructor
  · intro j; by_cases j = i <;> simp [*]
  · intro j; by_cases j = i <;> simp [*]; exact le_refl 1⟩

/-- For the toy space, effects span the full space (standard basis). -/
theorem toy_effect_span_top : ToySpace.effectSpan = ⊤ := by
  rw [OrderedUnitSpace.effectSpan, eq_top_iff]
  intro v _
  have : v = Finset.univ.sum fun i => (v i) • (effectAt i : Fin n → ℝ) := by
    ext j; simp [effectAt, Finset.sum_apply, Finset.mem_univ, ← Finset.sum_eq_single j]
  rw [this]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply subset_span
  use effectAt i
  rfl

/-- A state is a probability distribution: nonnegative, sums to 1. -/
def classicalState (f : Fin n → ℝ) (hsum : Finset.univ.sum f = 1) (hnn : ∀ i, 0 ≤ f i) :
    ToySpace.State where
  toFun := {
    toFun := fun g => Finset.univ.sum fun i => f i * g i
    map_add' := fun _ _ => by simp only [Finset.sum_add_distrib, add_mul, Pi.add_apply]
    map_smul' := fun c g => by simp only [Finset.mul_sum, RingHom.id_apply, smul_eq_mul, Finset.sum_congr rfl fun i _ => mul_left_comm c (f i) (g i)] }
  nonneg' := by intro g hg; simp only [LinearMap.coe_mk]; apply Finset.sum_nonneg; intro i _; exact mul_nonneg (hnn i) (hg i)
  norm_one := by simp [toyOrderUnit, hsum]

/-- Probability of effect e in classical state f is the dot product. -/
theorem classical_prob (f : Fin n → ℝ) (hsum : Finset.univ.sum f = 1) (hnn : ∀ i, 0 ≤ f i)
    (ω := classicalState f hsum hnn) (e : ToySpace.Effect) :
    ω.prob e = Finset.univ.sum fun i => f i * (e : Fin n → ℝ) i := rfl

/-- Closure axioms hold for the classical simplex (state gives additive, normalized assignment). -/
theorem closure_axioms_hold (f : Fin n → ℝ) (hsum : Finset.univ.sum f = 1) (hnn : ∀ i, 0 ≤ f i) :
    let ω := classicalState f hsum hnn
    ∀ (k : ℕ) (m : ToySpace.Measurement k), (Finset.univ.sum fun i => ω.prob (m.outcomes i)) = 1 := by
  intro ω k m
  simp only [State.prob, State.coe_apply, classicalState, LinearMap.coe_mk]
  rw [← Finset.sum_comm, Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => rfl]
  rw [← Finset.sum_comm, m.sum_eq_unit]
  simp [toyOrderUnit, hsum]

end GPTClosure.Examples.Toy
