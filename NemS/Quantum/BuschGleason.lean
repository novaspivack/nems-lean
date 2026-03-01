import NemS.Quantum.Measures
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# NemS.Quantum.BuschGleason

The Busch/Gleason representation theorem: any normalized, finitely additive
probability assignment on quantum effects is representable as
  μ(E) = Re(Tr(ρ·E))
for a unique density operator ρ.

## Proof status

**Uniqueness** (`busch_gleason_unique`): COMPLETE — 0 sorrys.
Full proof using three families of test effects (diagonal, real off-diagonal,
imaginary off-diagonal), extracting each matrix entry of ρ from the trace.

**Existence** (`busch_gleason`): 1 sorry (line ~310) — the Busch/Gleason
representation theorem. The proof requires: (1) extending μ to a bounded linear
functional on Herm(n) via POVM decomposition, (2) Hilbert–Schmidt Riesz
representation on the finite-dimensional real inner product space Herm(n).
This is the mathematical content of Gleason (1957) / Busch (1999).

All supporting infrastructure is fully proved with zero sorrys.
-/

namespace NemS
namespace Quantum

open BigOperators

-- ============================================================
-- Key shared helper: ite_and decomposition
-- ============================================================

private lemma ite_and_split {P Q : Prop} [Decidable P] [Decidable Q] :
    (if P ∧ Q then (1:ℂ) else 0) = (if P then 1 else 0) * (if Q then 1 else 0) := by
  split_ifs <;> simp_all

-- ============================================================
-- Density operator
-- ============================================================

/-- A density operator: Hermitian, positive semidefinite, trace 1. -/
structure DensityOp (n : ℕ) where
  ρ : Op n
  hermitian : ρ.IsHermitian
  psd : IsPosSemidef ρ
  trace_one : opTrace ρ = 1

-- ============================================================
-- Computational lemmas
-- ============================================================

/-- Tr(A · single(i₀,j₀)) = A j₀ i₀. -/
private lemma trace_mul_single {n : ℕ} (A : Op n) (i₀ j₀ : Fin n) :
    opTrace (A * Matrix.single i₀ j₀ (1:ℂ)) = A j₀ i₀ := by
  rw [opTrace, Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
  have inner : ∀ x : Fin n, ∑ x₁ : Fin n,
      (if i₀ = x ∧ j₀ = x₁ then (1:ℂ) else 0) * A x₁ x = if i₀ = x then A j₀ x else 0 := by
    intro x
    by_cases hx : i₀ = x
    · subst hx; simp [Finset.sum_ite_eq]
    · simp only [hx, false_and, ite_false, zero_mul, Finset.sum_const_zero, if_false]
  simp_rw [inner, eq_comm (a := i₀)]
  simp [Finset.sum_ite_eq]

private lemma trace_single_diag {n : ℕ} (A : Op n) (i : Fin n) :
    opTrace (A * Matrix.single i i (1:ℂ)) = A i i := trace_mul_single A i i

/-- For Hermitian A, diagonal entries are real. -/
private lemma hermitian_diag_real {n : ℕ} {A : Op n} (hA : A.IsHermitian) (i : Fin n) :
    (A i i).im = 0 := by
  have h := congr_fun (congr_fun hA i) i
  simp only [Matrix.conjTranspose_apply] at h
  have := congr_arg Complex.im h
  simp [Complex.conj_im] at this; linarith

/-- For Hermitian A, Re(A j i + A i j) = 2 Re(A i j). -/
private lemma hermitian_sym_re {n : ℕ} {A : Op n} (hA : A.IsHermitian) (i j : Fin n) :
    (A j i + A i j).re = 2 * (A i j).re := by
  have h := congr_fun (congr_fun hA j) i
  simp only [Matrix.conjTranspose_apply] at h
  rw [← h]; simp [Complex.add_re, Complex.star_def, Complex.conj_re]; ring

/-- For Hermitian A, Re(-i·(A j i) + i·(A i j)) = -2 Im(A i j). -/
private lemma hermitian_antisym_im {n : ℕ} {A : Op n} (hA : A.IsHermitian) (i j : Fin n) :
    (-(Complex.I * A j i) + Complex.I * A i j).re = -2 * (A i j).im := by
  have h := congr_fun (congr_fun hA j) i
  simp only [Matrix.conjTranspose_apply] at h
  rw [← h]; simp [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.I_im,
                   Complex.star_def, Complex.conj_re, Complex.conj_im]; ring

/-- Non-negativity of |v k|². -/
private lemma conj_mul_re_nonneg {n : ℕ} (v : Fin n → ℂ) (k : Fin n) :
    (0 : ℝ) ≤ (starRingEnd ℂ (v k) * v k).re := by
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (v k).re, sq_nonneg (v k).im]

-- ============================================================
-- Key summing helper
-- ============================================================

/-- When i ≠ a, the conditional sum is zero. -/
private lemma sum_ite_eq_zero_of_ne {n : ℕ} (v : Fin n → ℂ) (i a : Fin n)
    (ha : i ≠ a) (f : Fin n → ℂ) :
    (∑ b : Fin n, starRingEnd ℂ (v a) * (if i = a ∧ i = b then (1:ℂ) else 0) * f b) = 0 := by
  apply Finset.sum_eq_zero; intro b _
  simp [show ¬(i = a) from ha]

/-- When i = a, the sum collapses to the single term. -/
private lemma sum_ite_eq_self {n : ℕ} (v : Fin n → ℂ) (i : Fin n) (f : Fin n → ℂ) :
    (∑ b : Fin n, starRingEnd ℂ (v i) * (if i = i ∧ i = b then (1:ℂ) else 0) * f b) =
    starRingEnd ℂ (v i) * f i := by
  simp only [and_self]; simp_rw [mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq]

-- ============================================================
-- diagEffect: |i⟩⟨i| as a valid Effect
-- ============================================================

private def diagEffect {n : ℕ} (i : Fin n) : Effect n where
  op := Matrix.single i i (1:ℂ)
  hermitian := by
    ext a b; simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
    simp only [and_comm (a := i = b) (b := i = a)]
    split_ifs <;> simp [star_one, star_zero]
  psd := by
    constructor
    · ext a b; simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
      simp only [and_comm (a := i = b) (b := i = a)]
      split_ifs <;> simp [star_one, star_zero]
    · intro v
      simp only [sesqForm, Matrix.single_apply]
      have : (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) *
          (if i = a ∧ i = b then (1:ℂ) else 0) * v b) = starRingEnd ℂ (v i) * v i := by
        conv_lhs => rw [show (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) *
            (if i = a ∧ i = b then (1:ℂ) else 0) * v b) =
            ∑ a : Fin n, if i = a then starRingEnd ℂ (v i) * v i else 0 from by
          apply Finset.sum_congr rfl; intro a _
          by_cases ha : i = a
          · subst ha; simp only [if_true, and_self]; simp_rw [mul_ite, mul_one, mul_zero]; simp
          · simp only [ha, if_false]
            apply Finset.sum_eq_zero; intro b _; simp [ha]]
        simp [Finset.sum_ite_eq]
      rw [this]; exact conj_mul_re_nonneg v i
  bounded := by
    constructor
    · apply Matrix.IsHermitian.sub Matrix.isHermitian_one
      ext a b; simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
      simp only [and_comm (a := i = b) (b := i = a)]
      split_ifs <;> simp [star_one, star_zero]
    · intro v
      simp only [sesqForm, Matrix.sub_apply, Matrix.one_apply, Matrix.single_apply]
      have eq1 : ∀ a : Fin n, (∑ b : Fin n, starRingEnd ℂ (v a) * (if a = b then (1:ℂ) else 0) * v b) =
          starRingEnd ℂ (v a) * v a := by
        intro a; simp_rw [mul_ite, mul_one, mul_zero]; simp
      have eq2 : ∀ a : Fin n, (∑ b : Fin n, starRingEnd ℂ (v a) * (if i = a ∧ i = b then (1:ℂ) else 0) * v b) =
          if i = a then starRingEnd ℂ (v i) * v i else 0 := by
        intro a
        by_cases ha : i = a
        · subst ha; simp only [if_true, and_self]; simp_rw [mul_ite, mul_one, mul_zero]; simp
        · simp only [ha, if_false]
          apply Finset.sum_eq_zero; intro b _; simp [ha]
      -- LHS = ‖v‖² - |v i|² ≥ 0
      have rw1 : (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) *
          ((if a = b then (1:ℂ) else 0) - (if i = a ∧ i = b then 1 else 0)) * v b) =
          (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) * (if a = b then 1 else 0) * v b) -
          (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) * (if i = a ∧ i = b then 1 else 0) * v b) := by
        simp_rw [show ∀ a b : Fin n, starRingEnd ℂ (v a) *
            ((if a = b then (1:ℂ) else 0) - (if i = a ∧ i = b then 1 else 0)) * v b =
            starRingEnd ℂ (v a) * (if a = b then 1 else 0) * v b -
            starRingEnd ℂ (v a) * (if i = a ∧ i = b then 1 else 0) * v b from fun a b => by ring,
            Finset.sum_sub_distrib]
      rw [rw1, Complex.sub_re]
      have lhs1 : (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) * (if a = b then (1:ℂ) else 0) * v b).re =
          ∑ k : Fin n, (starRingEnd ℂ (v k) * v k).re := by
        rw [Complex.re_sum]; apply Finset.sum_congr rfl; intro a _; rw [eq1]
      have lhs2 : (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) * (if i = a ∧ i = b then (1:ℂ) else 0) * v b).re =
          (starRingEnd ℂ (v i) * v i).re := by
        have : (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) * (if i = a ∧ i = b then (1:ℂ) else 0) * v b) =
            starRingEnd ℂ (v i) * v i := by
          conv_lhs => rw [show (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) *
              (if i = a ∧ i = b then (1:ℂ) else 0) * v b) =
              ∑ a : Fin n, if i = a then starRingEnd ℂ (v i) * v i else 0 from by
            apply Finset.sum_congr rfl; intro a _; exact eq2 a]
          simp [Finset.sum_ite_eq]
        rw [this]
      rw [lhs1, lhs2]
      linarith [Finset.single_le_sum (s := Finset.univ)
                (f := fun k => (starRingEnd ℂ (v k) * v k).re)
                (fun k _ => conj_mul_re_nonneg v k) (Finset.mem_univ i)]

-- ============================================================
-- Key normSq computation helper for test effects
-- ============================================================

/-- Reduce the 4-term sum to (1/2) * normSq(v i + v j). -/
private lemma sum_to_normSq_R {n : ℕ} (i j : Fin n) (v : Fin n → ℂ) :
    (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) *
        ((1/2 : ℂ) * ((if i = a ∧ i = b then 1 else 0) + (if i = a ∧ j = b then 1 else 0) +
         (if j = a ∧ i = b then 1 else 0) + (if j = a ∧ j = b then 1 else 0))) * v b).re =
    (1/2 : ℝ) * Complex.normSq (v i + v j) := by
  have h1 : ∀ a b : Fin n, starRingEnd ℂ (v a) *
      ((1/2 : ℂ) * ((if i = a ∧ i = b then (1:ℂ) else 0) + (if i = a ∧ j = b then 1 else 0) +
       (if j = a ∧ i = b then 1 else 0) + (if j = a ∧ j = b then 1 else 0))) * v b =
      (1/2 : ℂ) * ((if i = a then (1:ℂ) else 0) * (if i = b then starRingEnd ℂ (v a) * v b else 0) +
                   (if i = a then 1 else 0) * (if j = b then starRingEnd ℂ (v a) * v b else 0) +
                   (if j = a then 1 else 0) * (if i = b then starRingEnd ℂ (v a) * v b else 0) +
                   (if j = a then 1 else 0) * (if j = b then starRingEnd ℂ (v a) * v b else 0)) := by
    intro a b; simp_rw [ite_and_split]; split_ifs <;> ring
  simp_rw [h1, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [← Finset.sum_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, one_mul, mul_one]
  -- Compute: (1/2 * (conj(vi)*vi + conj(vi)*vj + conj(vj)*vi + conj(vj)*vj)).re = (1/2)|vi+vj|²
  simp only [starRingEnd, map_add, map_mul, starRingAut_apply, Complex.star_def]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
             Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
             Complex.div_re, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
             Complex.star_def, Complex.conj_re, Complex.conj_im]
  norm_num; ring

/-- Reduce the Q-sum to (1/2) * normSq(v i - I * v j). -/
private lemma sum_to_normSq_Q {n : ℕ} (i j : Fin n) (v : Fin n → ℂ) :
    (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) *
        ((1/2 : ℂ) * ((if i = a ∧ i = b then 1 else 0) +
         (-Complex.I) * (if i = a ∧ j = b then 1 else 0) +
         Complex.I * (if j = a ∧ i = b then 1 else 0) +
         (if j = a ∧ j = b then 1 else 0))) * v b).re =
    (1/2 : ℝ) * Complex.normSq (v i - Complex.I * v j) := by
  have h1 : ∀ a b : Fin n, starRingEnd ℂ (v a) *
      ((1/2 : ℂ) * ((if i = a ∧ i = b then (1:ℂ) else 0) +
       (-Complex.I) * (if i = a ∧ j = b then 1 else 0) +
       Complex.I * (if j = a ∧ i = b then 1 else 0) +
       (if j = a ∧ j = b then 1 else 0))) * v b =
      (1/2 : ℂ) * ((if i = a then (1:ℂ) else 0) * (if i = b then starRingEnd ℂ (v a) * v b else 0) +
                   (-Complex.I) * ((if i = a then 1 else 0) * (if j = b then starRingEnd ℂ (v a) * v b else 0)) +
                   Complex.I * ((if j = a then 1 else 0) * (if i = b then starRingEnd ℂ (v a) * v b else 0)) +
                   (if j = a then 1 else 0) * (if j = b then starRingEnd ℂ (v a) * v b else 0)) := by
    intro a b; simp_rw [ite_and_split]; split_ifs <;> ring
  simp_rw [h1, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [← Finset.sum_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, one_mul, mul_one]
  simp only [starRingEnd, map_add, map_mul, starRingAut_apply, Complex.star_def]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
             Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
             Complex.div_re, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im,
             Complex.sub_re, Complex.sub_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  norm_num; ring

-- ============================================================
-- Bounded helper for R and Q effects
-- ============================================================

/-- sesqForm(I - R, v) ≥ 0: ‖v‖² ≥ (1/2)|v_i + v_j|² when i ≠ j. -/
private lemma R_bounded_psd {n : ℕ} (i j : Fin n) (hij : i ≠ j) (v : Fin n → ℂ) :
    (0 : ℝ) ≤ (sesqForm (1 - (1/2 : ℂ) • (Matrix.single i i (1:ℂ) + Matrix.single i j (1:ℂ) +
                                Matrix.single j i (1:ℂ) + Matrix.single j j (1:ℂ))) v).re := by
  simp only [sesqForm, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.add_apply,
             Matrix.single_apply, smul_eq_mul]
  -- Compute LHS = ‖v‖² - (1/2)|vi+vj|²
  have lhs_val : (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) *
      ((if a = b then (1:ℂ) else 0) - (1/2 : ℂ) * ((if i = a ∧ i = b then 1 else 0) +
       (if i = a ∧ j = b then 1 else 0) + (if j = a ∧ i = b then 1 else 0) +
       (if j = a ∧ j = b then 1 else 0))) * v b).re =
      (∑ k : Fin n, (starRingEnd ℂ (v k) * v k).re) -
      (1/2 : ℝ) * Complex.normSq (v i + v j) := by
    have eq1 : ∀ a : Fin n, (∑ b : Fin n, starRingEnd ℂ (v a) * (if a = b then (1:ℂ) else 0) * v b) =
        starRingEnd ℂ (v a) * v a := by
      intro a; simp_rw [mul_ite, mul_one, mul_zero]; simp
    have eq_R : (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) *
        ((1/2 : ℂ) * ((if i = a ∧ i = b then (1:ℂ) else 0) + (if i = a ∧ j = b then 1 else 0) +
         (if j = a ∧ i = b then 1 else 0) + (if j = a ∧ j = b then 1 else 0))) * v b).re =
        (1/2 : ℝ) * Complex.normSq (v i + v j) := sum_to_normSq_R i j v
    -- Split into two sums and compute each
    have hsplit : (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) *
        ((if a = b then (1:ℂ) else 0) - (1/2 : ℂ) * ((if i = a ∧ i = b then 1 else 0) +
         (if i = a ∧ j = b then 1 else 0) + (if j = a ∧ i = b then 1 else 0) +
         (if j = a ∧ j = b then 1 else 0))) * v b) =
        (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) * (if a = b then 1 else 0) * v b) -
        (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) * ((1/2 : ℂ) * ((if i = a ∧ i = b then 1 else 0) +
         (if i = a ∧ j = b then 1 else 0) + (if j = a ∧ i = b then 1 else 0) +
         (if j = a ∧ j = b then 1 else 0))) * v b) := by
      simp_rw [show ∀ a b : Fin n, starRingEnd ℂ (v a) *
          ((if a = b then (1:ℂ) else 0) - (1/2 : ℂ) * ((if i = a ∧ i = b then 1 else 0) +
           (if i = a ∧ j = b then 1 else 0) + (if j = a ∧ i = b then 1 else 0) +
           (if j = a ∧ j = b then 1 else 0))) * v b =
          starRingEnd ℂ (v a) * (if a = b then 1 else 0) * v b -
          starRingEnd ℂ (v a) * ((1/2 : ℂ) * ((if i = a ∧ i = b then 1 else 0) +
           (if i = a ∧ j = b then 1 else 0) + (if j = a ∧ i = b then 1 else 0) +
           (if j = a ∧ j = b then 1 else 0))) * v b from fun a b => by ring,
          Finset.sum_sub_distrib]
    rw [hsplit, Complex.sub_re, eq_R]
    congr 1
    rw [Complex.re_sum]; apply Finset.sum_congr rfl; intro a _
    rw [eq1]
  rw [lhs_val]
  have hpos : ∀ k : Fin n, (0:ℝ) ≤ (starRingEnd ℂ (v k) * v k).re := fun k => by
    have : (starRingEnd ℂ (v k) * v k).re = (v k).re ^ 2 + (v k).im ^ 2 := by
      simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, sq]
    rw [this]; nlinarith [sq_nonneg (v k).re, sq_nonneg (v k).im]
  have norm_ineq : (1/2 : ℝ) * Complex.normSq (v i + v j) ≤
      (starRingEnd ℂ (v i) * v i).re + (starRingEnd ℂ (v j) * v j).re := by
    have h1 : (starRingEnd ℂ (v i) * v i).re = (v i).re ^ 2 + (v i).im ^ 2 := by
      simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, sq]
    have h2 : (starRingEnd ℂ (v j) * v j).re = (v j).re ^ 2 + (v j).im ^ 2 := by
      simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, sq]
    rw [h1, h2]; simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
    nlinarith [sq_nonneg ((v i).re - (v j).re), sq_nonneg ((v i).im - (v j).im)]
  have pair_le : (starRingEnd ℂ (v i) * v i).re + (starRingEnd ℂ (v j) * v j).re ≤
      ∑ k : Fin n, (starRingEnd ℂ (v k) * v k).re := by
    have hpair : (starRingEnd ℂ (v i) * v i).re + (starRingEnd ℂ (v j) * v j).re =
        ∑ k ∈ ({i, j} : Finset (Fin n)), (starRingEnd ℂ (v k) * v k).re := by
      simp [Finset.sum_pair hij]
    rw [hpair]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro k _ _; exact hpos k
  linarith

/-- sesqForm(I - Q, v) ≥ 0: ‖v‖² ≥ (1/2)|v_i - I·v_j|² when i ≠ j. -/
private lemma Q_bounded_psd {n : ℕ} (i j : Fin n) (hij : i ≠ j) (v : Fin n → ℂ) :
    (0 : ℝ) ≤ (sesqForm (1 - (1/2 : ℂ) • (Matrix.single i i (1:ℂ) + (-Complex.I) • Matrix.single i j (1:ℂ) +
                                Complex.I • Matrix.single j i (1:ℂ) + Matrix.single j j (1:ℂ))) v).re := by
  simp only [sesqForm, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.add_apply,
             Matrix.single_apply, smul_eq_mul]
  have eq1 : ∀ a : Fin n, (∑ b : Fin n, starRingEnd ℂ (v a) * (if a = b then (1:ℂ) else 0) * v b) =
      starRingEnd ℂ (v a) * v a := by
    intro a; simp_rw [mul_ite, mul_one, mul_zero]; simp
  have eq_Q : (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) *
      ((1/2 : ℂ) * ((if i = a ∧ i = b then (1:ℂ) else 0) +
       (-Complex.I) * (if i = a ∧ j = b then 1 else 0) +
       Complex.I * (if j = a ∧ i = b then 1 else 0) +
       (if j = a ∧ j = b then 1 else 0))) * v b).re =
      (1/2 : ℝ) * Complex.normSq (v i - Complex.I * v j) := sum_to_normSq_Q i j v
  have rw1 : (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) *
      ((if a = b then (1:ℂ) else 0) - (1/2 : ℂ) * ((if i = a ∧ i = b then 1 else 0) +
       (-Complex.I) * (if i = a ∧ j = b then 1 else 0) + Complex.I * (if j = a ∧ i = b then 1 else 0) +
       (if j = a ∧ j = b then 1 else 0))) * v b) =
      (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) * (if a = b then 1 else 0) * v b) -
      (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) * ((1/2 : ℂ) * ((if i = a ∧ i = b then 1 else 0) +
       (-Complex.I) * (if i = a ∧ j = b then 1 else 0) + Complex.I * (if j = a ∧ i = b then 1 else 0) +
       (if j = a ∧ j = b then 1 else 0))) * v b) := by
    simp_rw [show ∀ a b : Fin n, starRingEnd ℂ (v a) *
        ((if a = b then (1:ℂ) else 0) - (1/2 : ℂ) * ((if i = a ∧ i = b then 1 else 0) +
         (-Complex.I) * (if i = a ∧ j = b then 1 else 0) + Complex.I * (if j = a ∧ i = b then 1 else 0) +
         (if j = a ∧ j = b then 1 else 0))) * v b =
        starRingEnd ℂ (v a) * (if a = b then 1 else 0) * v b -
        starRingEnd ℂ (v a) * ((1/2 : ℂ) * ((if i = a ∧ i = b then 1 else 0) +
         (-Complex.I) * (if i = a ∧ j = b then 1 else 0) + Complex.I * (if j = a ∧ i = b then 1 else 0) +
         (if j = a ∧ j = b then 1 else 0))) * v b from fun a b => by ring,
        Finset.sum_sub_distrib]
  -- Compute LHS = ‖v‖² - (1/2)|vi - I*vj|² and show ≥ 0
  have lhs_val2 : (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) *
      ((if a = b then (1:ℂ) else 0) - (1/2 : ℂ) * ((if i = a ∧ i = b then 1 else 0) +
       (-Complex.I) * (if i = a ∧ j = b then 1 else 0) + Complex.I * (if j = a ∧ i = b then 1 else 0) +
       (if j = a ∧ j = b then 1 else 0))) * v b).re =
      (∑ k : Fin n, (starRingEnd ℂ (v k) * v k).re) -
      (1/2 : ℝ) * Complex.normSq (v i - Complex.I * v j) := by
    rw [show (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) *
        ((if a = b then (1:ℂ) else 0) - (1/2 : ℂ) * ((if i = a ∧ i = b then 1 else 0) +
         (-Complex.I) * (if i = a ∧ j = b then 1 else 0) + Complex.I * (if j = a ∧ i = b then 1 else 0) +
         (if j = a ∧ j = b then 1 else 0))) * v b) =
        (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) * (if a = b then 1 else 0) * v b) -
        (∑ a : Fin n, ∑ b : Fin n, starRingEnd ℂ (v a) * ((1/2 : ℂ) * ((if i = a ∧ i = b then 1 else 0) +
         (-Complex.I) * (if i = a ∧ j = b then 1 else 0) + Complex.I * (if j = a ∧ i = b then 1 else 0) +
         (if j = a ∧ j = b then 1 else 0))) * v b) from by
      simp_rw [show ∀ a b : Fin n, starRingEnd ℂ (v a) *
          ((if a = b then (1:ℂ) else 0) - (1/2 : ℂ) * ((if i = a ∧ i = b then 1 else 0) +
           (-Complex.I) * (if i = a ∧ j = b then 1 else 0) + Complex.I * (if j = a ∧ i = b then 1 else 0) +
           (if j = a ∧ j = b then 1 else 0))) * v b =
          starRingEnd ℂ (v a) * (if a = b then 1 else 0) * v b -
          starRingEnd ℂ (v a) * ((1/2 : ℂ) * ((if i = a ∧ i = b then 1 else 0) +
           (-Complex.I) * (if i = a ∧ j = b then 1 else 0) + Complex.I * (if j = a ∧ i = b then 1 else 0) +
           (if j = a ∧ j = b then 1 else 0))) * v b from fun a b => by ring,
           Finset.sum_sub_distrib]]
    rw [Complex.sub_re, eq_Q]
    congr 1; rw [Complex.re_sum]; apply Finset.sum_congr rfl; intro a _; rw [eq1]
  rw [lhs_val2]
  have hpos : ∀ k : Fin n, (0:ℝ) ≤ (starRingEnd ℂ (v k) * v k).re := fun k => by
    have : (starRingEnd ℂ (v k) * v k).re = (v k).re ^ 2 + (v k).im ^ 2 := by
      simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, sq]
    rw [this]; nlinarith [sq_nonneg (v k).re, sq_nonneg (v k).im]
  have norm_ineq : (1/2 : ℝ) * Complex.normSq (v i - Complex.I * v j) ≤
      (starRingEnd ℂ (v i) * v i).re + (starRingEnd ℂ (v j) * v j).re := by
    have h1 : (starRingEnd ℂ (v i) * v i).re = (v i).re ^ 2 + (v i).im ^ 2 := by
      simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, sq]
    have h2 : (starRingEnd ℂ (v j) * v j).re = (v j).re ^ 2 + (v j).im ^ 2 := by
      simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, sq]
    rw [h1, h2]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
               Complex.I_re, Complex.I_im]
    nlinarith [sq_nonneg ((v i).re - (v j).im), sq_nonneg ((v i).im + (v j).re)]
  have pair_le : (starRingEnd ℂ (v i) * v i).re + (starRingEnd ℂ (v j) * v j).re ≤
      ∑ k : Fin n, (starRingEnd ℂ (v k) * v k).re := by
    have hpair : (starRingEnd ℂ (v i) * v i).re + (starRingEnd ℂ (v j) * v j).re =
        ∑ k ∈ ({i, j} : Finset (Fin n)), (starRingEnd ℂ (v k) * v k).re := by
      simp [Finset.sum_pair hij]
    rw [hpair]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro k _ _; exact hpos k
  linarith

-- ============================================================
-- Test effects for off-diagonal uniqueness
-- ============================================================

/-- Real test effect: (1/2)(|i⟩+|j⟩)(⟨i|+⟨j|), for i ≠ j.
sesqForm = (1/2)|v_i + v_j|² ≥ 0. -/
private noncomputable def realTestEff {n : ℕ} (i j : Fin n) (hij : i ≠ j) : Effect n where
  op := (1/2 : ℂ) • (Matrix.single i i (1:ℂ) + Matrix.single i j (1:ℂ) +
                       Matrix.single j i (1:ℂ) + Matrix.single j j (1:ℂ))
  hermitian := by
    ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply,
               Matrix.single_apply, smul_eq_mul]
    simp only [and_comm (a := i = b) (b := i = a), and_comm (a := i = b) (b := j = a),
               and_comm (a := j = b) (b := i = a), and_comm (a := j = b) (b := j = a)]
    split_ifs <;> simp [star_smul, star_one, star_zero]
  psd := by
    constructor
    · ext a b
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply,
                 Matrix.single_apply, smul_eq_mul]
      simp only [and_comm (a := i = b) (b := i = a), and_comm (a := i = b) (b := j = a),
                 and_comm (a := j = b) (b := i = a), and_comm (a := j = b) (b := j = a)]
      split_ifs <;> simp [star_smul, star_one, star_zero]
    · intro v
      simp only [sesqForm, Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul]
      rw [sum_to_normSq_R]
      exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
  bounded := by
    constructor
    · apply Matrix.IsHermitian.sub Matrix.isHermitian_one
      ext a b
      simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply,
                 Matrix.single_apply, smul_eq_mul]
      simp only [and_comm (a := i = b) (b := i = a), and_comm (a := i = b) (b := j = a),
                 and_comm (a := j = b) (b := i = a), and_comm (a := j = b) (b := j = a)]
      split_ifs <;> simp [star_smul, star_one, star_zero]
    · intro v
      exact R_bounded_psd i j hij v

/-- Imaginary test effect: (1/2)(|i⟩+i|j⟩)(⟨i|-i⟨j|), for i ≠ j.
sesqForm = (1/2)|v_i - i·v_j|² ≥ 0. -/
private noncomputable def imagTestEff {n : ℕ} (i j : Fin n) (hij : i ≠ j) : Effect n where
  op := (1/2 : ℂ) • (Matrix.single i i (1:ℂ) + (-Complex.I) • Matrix.single i j (1:ℂ) +
                       Complex.I • Matrix.single j i (1:ℂ) + Matrix.single j j (1:ℂ))
  hermitian := by
    ext a b; simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul,
                         Matrix.conjTranspose_apply, Matrix.single_apply]
    simp only [and_comm (a := i = b) (b := i = a), and_comm (a := i = b) (b := j = a),
               and_comm (a := j = b) (b := i = a), and_comm (a := j = b) (b := j = a)]
    split_ifs <;> simp [star_smul, star_neg, Complex.star_def, Complex.conj_ofReal, Complex.I_sq]
  psd := by
    constructor
    · ext a b; simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul,
                           Matrix.conjTranspose_apply, Matrix.single_apply]
      simp only [and_comm (a := i = b) (b := i = a), and_comm (a := i = b) (b := j = a),
                 and_comm (a := j = b) (b := i = a), and_comm (a := j = b) (b := j = a)]
      split_ifs <;> simp [star_smul, star_neg, Complex.star_def, Complex.conj_ofReal, Complex.I_sq]
    · intro v
      simp only [sesqForm, Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul]
      rw [sum_to_normSq_Q]
      exact mul_nonneg (by norm_num) (Complex.normSq_nonneg _)
  bounded := by
    constructor
    · apply Matrix.IsHermitian.sub Matrix.isHermitian_one
      ext a b; simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul,
                           Matrix.conjTranspose_apply, Matrix.single_apply]
      simp only [and_comm (a := i = b) (b := i = a), and_comm (a := i = b) (b := j = a),
                 and_comm (a := j = b) (b := i = a), and_comm (a := j = b) (b := j = a)]
      split_ifs <;> simp [star_smul, star_neg, Complex.star_def, Complex.conj_ofReal, Complex.I_sq]
    · intro v
      exact Q_bounded_psd i j hij v

-- ============================================================
-- Trace computations for test effects
-- ============================================================

private lemma trace_realTestEff {n : ℕ} (A : Op n) (i j : Fin n) (hij : i ≠ j) :
    opTrace (A * (realTestEff i j hij).op) = (1/2 : ℂ) *
        (A i i + A j i + A i j + A j j) := by
  -- (realTestEff i j hij).op definitionally equals the smul expression
  have hR : (realTestEff i j hij).op = (1/2 : ℂ) • (Matrix.single i i (1:ℂ) +
      Matrix.single i j (1:ℂ) + Matrix.single j i (1:ℂ) + Matrix.single j j (1:ℂ)) := rfl
  -- Use opTrace linearity
  rw [hR, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add]
  -- Use opTrace linearity
  have h1 := trace_mul_single A i i
  have h2 := trace_mul_single A i j
  have h3 := trace_mul_single A j i
  have h4 := trace_mul_single A j j
  simp only [opTrace, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul] at *
  rw [h1, h2, h3, h4]

private lemma trace_imagTestEff {n : ℕ} (A : Op n) (i j : Fin n) (hij : i ≠ j) :
    opTrace (A * (imagTestEff i j hij).op) = (1/2 : ℂ) *
        (A i i + (-Complex.I) * A j i + Complex.I * A i j + A j j) := by
  have hQ : (imagTestEff i j hij).op = (1/2 : ℂ) • (Matrix.single i i (1:ℂ) +
      (-Complex.I) • Matrix.single i j (1:ℂ) + Complex.I • Matrix.single j i (1:ℂ) +
      Matrix.single j j (1:ℂ)) := rfl
  rw [hQ, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add,
      Matrix.mul_smul, Matrix.mul_smul]
  have h1 := trace_mul_single A i i
  have h2 := trace_mul_single A i j
  have h3 := trace_mul_single A j i
  have h4 := trace_mul_single A j j
  simp only [opTrace, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul] at *
  rw [h1, h2, h3, h4]

-- ============================================================
-- Main theorems
-- ============================================================

/-- **Busch/Gleason existence** (1 sorry: the representation theorem).
This is the mathematical content of Busch (1999) / Gleason (1957).
Proof sketch: define ρ_ij from μ via test effects, verify Born rule on all effects
using the fact that both μ and Re(Tr(ρ·)) are frame functions that agree on a
spanning set of Herm(n). -/
theorem busch_gleason {n : ℕ} (m : EffectMeasure n) :
    ∃ ρ : DensityOp n, ∀ E : Effect n, m.μ E = (opTrace (ρ.ρ * E.op)).re :=
  sorry

/-- **Busch/Gleason uniqueness** — FULLY PROVED, ZERO SORRYS.

Strategy: for each (i,j), use test effects to extract ρ_ij entry by entry.
- Diagonal: diagEffect i gives ρ ii = real.
- Off-diagonal real: realTestEff i j gives Re(ρ ij).
- Off-diagonal imaginary: imagTestEff i j gives Im(ρ ij).  -/
theorem busch_gleason_unique {n : ℕ} (m : EffectMeasure n)
    (ρ₁ ρ₂ : DensityOp n)
    (h₁ : ∀ E : Effect n, m.μ E = (opTrace (ρ₁.ρ * E.op)).re)
    (h₂ : ∀ E : Effect n, m.μ E = (opTrace (ρ₂.ρ * E.op)).re) :
    ρ₁.ρ = ρ₂.ρ := by
  have hE : ∀ E : Effect n, (opTrace (ρ₁.ρ * E.op)).re = (opTrace (ρ₂.ρ * E.op)).re :=
    fun E => by rw [← h₁, ← h₂]
  -- Step 1: diagonal entries equal (both real by hermitian_diag_real)
  have hdiag : ∀ k : Fin n, ρ₁.ρ k k = ρ₂.ρ k k := by
    intro k
    have := hE (diagEffect k)
    simp only [diagEffect, trace_single_diag] at this
    apply Complex.ext
    · exact this
    · simp [hermitian_diag_real ρ₁.hermitian, hermitian_diag_real ρ₂.hermitian]
  apply Matrix.ext; intro i j; apply Complex.ext
  · -- Real part
    by_cases hij : i = j
    · subst hij; exact (Complex.ext_iff.mp (hdiag i)).1
    · have hR := hE (realTestEff i j hij)
      rw [trace_realTestEff _ _ _ hij, trace_realTestEff _ _ _ hij] at hR
      have h1 := hermitian_sym_re ρ₁.hermitian i j
      have h2 := hermitian_sym_re ρ₂.hermitian i j
      have hii : (ρ₁.ρ i i).re = (ρ₂.ρ i i).re := (Complex.ext_iff.mp (hdiag i)).1
      have hjj : (ρ₁.ρ j j).re = (ρ₂.ρ j j).re := (Complex.ext_iff.mp (hdiag j)).1
      -- hR: Re(1/2 * (ρ₁ ii + ρ₁ ji + ρ₁ ij + ρ₁ jj)) = Re(1/2 * (ρ₂ ii + ρ₂ ji + ρ₂ ij + ρ₂ jj))
      -- Using hermitian: ρ ji + ρ ij = 2*Re(ρ ij) (real), so Re of each side = (1/2)(ρ_ii + 2*Re(ρ_ij) + ρ_jj)
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
                 Complex.div_re, Complex.one_re, Complex.one_im,
                 one_mul, zero_mul, sub_zero] at hR
      norm_num at hR
      simp only [Complex.add_re] at h1 h2
      linarith [hR, hii, hjj, h1, h2,
                hermitian_diag_real ρ₁.hermitian i, hermitian_diag_real ρ₁.hermitian j,
                hermitian_diag_real ρ₂.hermitian i, hermitian_diag_real ρ₂.hermitian j]
  · -- Imaginary part
    by_cases hij : i = j
    · subst hij
      simp [hermitian_diag_real ρ₁.hermitian, hermitian_diag_real ρ₂.hermitian]
    · have hQ := hE (imagTestEff i j hij)
      rw [trace_imagTestEff _ _ _ hij, trace_imagTestEff _ _ _ hij] at hQ
      have h1 := hermitian_antisym_im ρ₁.hermitian i j
      have h2 := hermitian_antisym_im ρ₂.hermitian i j
      have hii : (ρ₁.ρ i i).re = (ρ₂.ρ i i).re := (Complex.ext_iff.mp (hdiag i)).1
      have hjj : (ρ₁.ρ j j).re = (ρ₂.ρ j j).re := (Complex.ext_iff.mp (hdiag j)).1
      simp only [Complex.mul_re, Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.I_re,
                 Complex.I_im, one_mul, zero_mul, sub_zero, Complex.ofReal_re,
                 Complex.div_re, Complex.one_re, Complex.one_im] at hQ
      norm_num at hQ
      simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.I_im,
                 Complex.ofReal_re] at h1 h2
      linarith [hQ, hii, hjj, h1, h2,
                hermitian_diag_real ρ₁.hermitian i, hermitian_diag_real ρ₁.hermitian j,
                hermitian_diag_real ρ₂.hermitian i, hermitian_diag_real ρ₂.hermitian j]

/-- Born rule follows from existence. -/
theorem born_rule {n : ℕ} (m : EffectMeasure n) :
    ∃ ρ : DensityOp n, ∀ (P : Effect n), P.op * P.op = P.op →
      m.μ P = (opTrace (ρ.ρ * P.op)).re := by
  obtain ⟨ρ, hρ⟩ := busch_gleason m; exact ⟨ρ, fun P _ => hρ P⟩

/-- Sanity: (1/n)·I is a density operator. -/
theorem trivialDensityOp_exists (n : ℕ) (hn : n ≠ 0) :
    ∃ ρ : DensityOp n, ρ.ρ = (1 / (n : ℂ)) • (1 : Op n) := by
  refine ⟨⟨(1 / (n : ℂ)) • 1, ?_, ?_, ?_⟩, rfl⟩
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_smul]
  · constructor
    · simp [Matrix.IsHermitian, Matrix.conjTranspose_smul]
    · intro v
      have hI := (isPosSemidef_one (n := n)).2 v
      simp only [sesqForm, Matrix.smul_apply, Matrix.one_apply]
      -- sesqForm ((1/n)•I) v = (1/n) * sesqForm I v = (1/n) * ‖v‖² ≥ 0
      have factored : (∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (v i) *
          ((1 / ↑n : ℂ) • (if i = j then (1:ℂ) else 0)) * v j) =
          (1 / ↑n : ℂ) * ∑ i : Fin n, ∑ j : Fin n,
          starRingEnd ℂ (v i) * (if i = j then 1 else 0) * v j := by
        simp_rw [smul_eq_mul]
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
        ring
      rw [factored, Complex.mul_re]
      have h1 : (1 / ↑n : ℂ).re = 1 / n := by
        simp [Complex.div_re, Complex.one_re, Complex.one_im, Complex.normSq_natCast]
      have h2 : (1 / ↑n : ℂ).im = 0 := by
        simp [Complex.div_im, Complex.one_re, Complex.one_im]
      rw [h1, h2]
      have hone := (isPosSemidef_one (n := n)).2 v
      simp only [sesqForm, Matrix.one_apply] at hone
      have hn : (0 : ℝ) ≤ 1 / n := by positivity
      nlinarith
  · simp [opTrace, Matrix.trace_smul, Matrix.trace_one]
    field_simp [Nat.cast_ne_zero.mpr hn]

end Quantum
end NemS
