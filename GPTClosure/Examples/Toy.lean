-- Classical simplex: V = Fin n → ℝ, coordinatewise cone, u = 1 (Paper 39)
import GPTClosure.Core.OrderedSpaces
import GPTClosure.Core.EffectsStates
import GPTClosure.Core.Measurements
import GPTClosure.Theorems.Uniqueness
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card

open Submodule

variable (n : ℕ) [NeZero n]

namespace GPTClosure.Examples.Toy

def ToyCone (n : ℕ) : ConePredicate (Fin n → ℝ) where
  Pos f := ∀ i, 0 ≤ f i
  pos_zero := fun _ => le_refl 0
  pos_add := fun _ _ hf hg i => add_nonneg (hf i) (hg i)
  pos_smul := fun c _ hc hf i => mul_nonneg hc (hf i)
  pos_neg_iff_zero := fun f hf hneg => by
    ext i
    have h1 := hf i
    have h2 := hneg i
    simp only [Pi.neg_apply] at h2
    simp only [Pi.zero_apply]
    linarith

def toyOrderUnit (n : ℕ) : Fin n → ℝ := fun _ => 1

def ToySpace : OrderedUnitSpace (Fin n → ℝ) := {
  cone := ToyCone n
  orderUnit := toyOrderUnit n
  pos_order_unit := fun _ => zero_le_one
}

def effectAt (i : Fin n) : OrderedUnitSpace.Effect (ToySpace n) :=
  ⟨fun j => if j = i then 1 else 0, by
    constructor
    · intro j
      simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]
      split <;> linarith
    · intro j
      show 0 ≤ (toyOrderUnit n j) - (if j = i then (1 : ℝ) else 0)
      unfold toyOrderUnit
      split <;> linarith⟩

omit [NeZero n] in
private lemma toy_sum_basis (v : Fin n → ℝ) (j : Fin n) :
    (Finset.univ.sum fun i => v i * if j = i then (1 : ℝ) else 0) = v j := by
  have h1 : ∀ i ∈ Finset.univ, i ≠ j → v i * (if j = i then (1 : ℝ) else 0) = 0 := by
    intro i _ hi
    have : j ≠ i := fun h => hi h.symm
    rw [if_neg this, mul_zero]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j) (fun i hi hij => h1 i hi hij)]
  rw [if_pos rfl, mul_one]

omit [NeZero n] in
theorem toy_effect_span_top : OrderedUnitSpace.effectSpan (ToySpace n) = ⊤ := by
  unfold OrderedUnitSpace.effectSpan
  rw [eq_top_iff]
  intro v _
  have effectAt_val : ∀ (i j : Fin n), (effectAt n i).val j = if j = i then (1 : ℝ) else 0 :=
    fun _ _ => rfl
  have hv : v = Finset.univ.sum (fun i => (v i) • (effectAt n i).val) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (∑ x, v x * (effectAt n x).val j) = (∑ x, v x * if j = x then 1 else 0) from
      Finset.sum_congr rfl (fun i _ => by rw [effectAt_val i j])]
    exact (toy_sum_basis n v j).symm
  rw [hv]
  apply sum_mem
  intro i _
  apply smul_mem
  exact Submodule.subset_span ⟨effectAt n i, rfl⟩

def classicalState (f : Fin n → ℝ) (hsum : Finset.univ.sum f = 1) (hnn : ∀ i, 0 ≤ f i) :
    OrderedUnitSpace.State (ToySpace n) where
  toFun := {
    toFun := fun g => Finset.univ.sum fun i => f i * g i
    map_add' := fun g₁ g₂ => by
      simp only [Pi.add_apply, mul_add, ← Finset.sum_add_distrib]
    map_smul' := fun c g => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [Finset.mul_sum]
      congr 1; funext i; ring }
  nonneg' := fun g hg => by
    change 0 ≤ Finset.univ.sum (fun i => f i * g i)
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hnn i) (hg i)
  norm_one := by
    show (Finset.univ.sum fun i => f i * toyOrderUnit n i) = 1
    have : ∀ i, toyOrderUnit n i = 1 := fun _ => rfl
    simp_rw [this, mul_one]
    exact hsum

omit [NeZero n] in
theorem classical_prob (f : Fin n → ℝ) (hsum : Finset.univ.sum f = 1) (hnn : ∀ i, 0 ≤ f i)
    (e : OrderedUnitSpace.Effect (ToySpace n)) :
    (classicalState n f hsum hnn).toFun e.val =
      Finset.univ.sum fun i => f i * e.val i := rfl

omit [NeZero n] in
theorem closure_axioms_hold (f : Fin n → ℝ) (hsum : Finset.univ.sum f = 1) (hnn : ∀ i, 0 ≤ f i) :
    let ω := classicalState n f hsum hnn
    ∀ (k : ℕ) (m : OrderedUnitSpace.Measurement (ToySpace n) k),
      (Finset.univ.sum fun i => ω.toFun (m.outcomes i).val) = 1 := by
  intro ω k m
  show Finset.univ.sum (fun i => Finset.univ.sum (fun j => f j * ((m.outcomes i).val j))) = 1
  rw [Finset.sum_comm]
  have key : ∀ j, (Finset.univ.sum fun i => (m.outcomes i).val j) =
      (Finset.univ.sum fun i => (m.outcomes i).val) j :=
    fun j => (Finset.sum_apply j Finset.univ (fun i => (m.outcomes i).val)).symm
  simp_rw [← Finset.mul_sum, key, m.sum_eq_unit]
  show (Finset.univ.sum fun j => f j * (ToySpace n).orderUnit j) = 1
  have : (ToySpace n).orderUnit = toyOrderUnit n := rfl
  rw [this]
  have h2 : ∀ j, toyOrderUnit n j = 1 := fun _ => rfl
  simp_rw [h2, mul_one]
  exact hsum

end GPTClosure.Examples.Toy
