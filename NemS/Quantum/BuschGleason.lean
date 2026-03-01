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

**Existence** (`busch_gleason`): 2 remaining sorrys (`rhoCandidate_psd`,
`rhoCandidate_represents`) — both are the same core linear-extension step:
extend POVM additivity to a real-linear functional on Herm(n), then conclude
global representation and positivity via finite-dimensional Hilbert–Schmidt/Riesz.
This is the mathematical content of Gleason (1957) / Busch (1999/2003).

All test-effect extraction and delta/POVM-additivity infrastructure is fully proved.
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

private lemma realTestEff_symm {n : ℕ} (i j : Fin n) (hij : i ≠ j) (hji : j ≠ i) :
    (realTestEff i j hij).op = (realTestEff j i hji).op := by
  ext a b
  simp [realTestEff, Matrix.add_apply, Matrix.single_apply, smul_eq_mul, add_assoc, add_left_comm, add_comm]

private lemma imagTestEff_pair_sum {n : ℕ} (i j : Fin n) (hij : i ≠ j) (hji : j ≠ i) :
    (imagTestEff i j hij).op + (imagTestEff j i hji).op = (diagEffect i).op + (diagEffect j).op := by
  ext a b
  simp only [imagTestEff, diagEffect, Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul]
  ring

private lemma realTestEff_proof_irrel {n : ℕ} (i j : Fin n) (h1 h2 : i ≠ j) :
    realTestEff i j h1 = realTestEff i j h2 := by
  simp [realTestEff]

private lemma imagTestEff_proof_irrel {n : ℕ} (i j : Fin n) (h1 h2 : i ≠ j) :
    imagTestEff i j h1 = imagTestEff i j h2 := by
  simp [imagTestEff]

private lemma realTestEff_swap {n : ℕ} (i j : Fin n) (hij : i ≠ j) (hji : j ≠ i) :
    realTestEff i j hij = realTestEff j i hji := by
  simp [realTestEff, add_assoc, add_left_comm, add_comm]

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
-- Existence: construct ρ from μ
-- ============================================================

-- Step 1: Binary additivity
private lemma binary_additivity {n : ℕ} (m : EffectMeasure n) (E F : Effect n)
    (h : IsPosSemidef (1 - (E.op + F.op))) :
    m.μ (Effect.add E F h) = m.μ E + m.μ F := by
  set EF := Effect.add E F h
  have hcomp_bdd : IsPosSemidef (1 - (1 - (E.op + F.op))) := by
    simp only [sub_sub_cancel]; exact isPosSemidef_add E.psd F.psd
  set C : Effect n := ⟨1 - (E.op + F.op), h.1, h, hcomp_bdd⟩
  have hEF_op : EF.op = E.op + F.op := rfl
  have hC_op : C.op = 1 - (E.op + F.op) := rfl
  have hsum2 : (∑ i : Fin 2, (![EF, C] i).op) = 1 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [hEF_op, hC_op]; simp [add_sub_cancel]
  have hP2 := m.povm_additive (⟨![EF, C], hsum2⟩ : POVM n 2)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hP2
  have hsum3 : (∑ i : Fin 3, (![E, F, C] i).op) = 1 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
               Matrix.head_fin_const]
    show E.op + F.op + (1 - (E.op + F.op)) = 1; abel
  have hP3 := m.povm_additive (⟨![E, F, C], hsum3⟩ : POVM n 3)
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
             Matrix.head_fin_const] at hP3
  have : m.μ EF + m.μ C = 1 := hP2
  have : m.μ E + m.μ F + m.μ C = 1 := hP3
  linarith

-- Step 2: diagEffects sum to I (they form a POVM)
private lemma diagEffects_sum_one (n : ℕ) :
    (∑ i : Fin n, (diagEffect i).op) = 1 := by
  ext a b; simp only [Matrix.one_apply]
  rw [Finset.sum_apply, Finset.sum_apply]
  simp only [diagEffect, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab; simp [and_self, Finset.sum_ite_eq']
  · simp only [if_neg hab]
    apply Finset.sum_eq_zero; intro i _
    simp [show ¬(i = a ∧ i = b) from fun h => hab (h.1.symm.trans h.2)]

private lemma isPosSemidef_sum_diag {n : ℕ} (s : Finset (Fin n)) :
    IsPosSemidef (Finset.sum s (fun k => (diagEffect k).op)) := by
  refine Finset.induction_on s ?base ?step
  · simpa using isPosSemidef_zero
  · intro a s ha hs
    simpa [Finset.sum_insert ha] using isPosSemidef_add (diagEffect a).psd hs

private lemma diag_pair_complement_eq_sum {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (1 - ((diagEffect i).op + (diagEffect j).op)) =
      Finset.sum ((Finset.univ.erase i).erase j) (fun k => (diagEffect k).op) := by
  let f : Fin n → Op n := fun k => (diagEffect k).op
  have hsumAll : Finset.sum Finset.univ f = 1 := by
    simpa [f] using diagEffects_sum_one n
  have hEraseI :
      Finset.sum (Finset.univ.erase i) f + f i = Finset.sum Finset.univ f := by
    exact Finset.sum_erase_add (s := Finset.univ) (a := i) (f := f) (Finset.mem_univ i)
  have hjmem : j ∈ Finset.univ.erase i := by
    exact Finset.mem_erase.mpr ⟨by intro h; exact hij h.symm, Finset.mem_univ j⟩
  have hEraseIJ :
      Finset.sum ((Finset.univ.erase i).erase j) f + f j = Finset.sum (Finset.univ.erase i) f := by
    exact Finset.sum_erase_add (s := Finset.univ.erase i) (a := j) (f := f) hjmem
  have hsumPair :
      Finset.sum ((Finset.univ.erase i).erase j) f + (f i + f j) = 1 := by
    calc
      Finset.sum ((Finset.univ.erase i).erase j) f + (f i + f j)
          = (Finset.sum ((Finset.univ.erase i).erase j) f + f j) + f i := by
              abel
      _ = Finset.sum (Finset.univ.erase i) f + f i := by rw [hEraseIJ]
      _ = Finset.sum Finset.univ f := by rw [hEraseI]
      _ = 1 := hsumAll
  have hsumPair' :
      Finset.sum ((Finset.univ.erase i).erase j) f = 1 - (f i + f j) := by
    exact (eq_sub_iff_add_eq).2 hsumPair
  simpa [f, add_comm, add_left_comm, add_assoc] using hsumPair'.symm

private lemma diag_pair_bounded_psd {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    IsPosSemidef (1 - ((diagEffect i).op + (diagEffect j).op)) := by
  rw [diag_pair_complement_eq_sum i j hij]
  exact isPosSemidef_sum_diag ((Finset.univ.erase i).erase j)

private noncomputable def diagPairComplementEffect {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) : Effect n where
  op := 1 - ((diagEffect i).op + (diagEffect j).op)
  hermitian := by
    apply Matrix.IsHermitian.sub Matrix.isHermitian_one
    exact (diagEffect i).hermitian.add (diagEffect j).hermitian
  psd := diag_pair_bounded_psd i j hij
  bounded := by
    have hpsd : IsPosSemidef ((diagEffect i).op + (diagEffect j).op) :=
      isPosSemidef_add (diagEffect i).psd (diagEffect j).psd
    simpa [sub_sub_cancel] using hpsd

private lemma μ_imag_pair_sum {n : ℕ} (m : EffectMeasure n)
    {i j : Fin n} (hij : i ≠ j) :
    m.μ (imagTestEff i j hij) + m.μ (imagTestEff j i (fun h => hij h.symm)) =
      m.μ (diagEffect i) + m.μ (diagEffect j) := by
  let hji : j ≠ i := fun h => hij h.symm
  let C : Effect n := diagPairComplementEffect i j hij
  have hsumQ : (∑ t : Fin 3, (![imagTestEff i j hij, imagTestEff j i hji, C] t).op) = 1 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const]
    rw [imagTestEff_pair_sum i j hij hji]
    show (diagEffect i).op + (diagEffect j).op + (diagPairComplementEffect i j hij).op = 1
    simp [diagPairComplementEffect]
  have hsumD : (∑ t : Fin 3, (![diagEffect i, diagEffect j, C] t).op) = 1 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.head_fin_const]
    show (diagEffect i).op + (diagEffect j).op + (diagPairComplementEffect i j hij).op = 1
    simp [diagPairComplementEffect]
  have hQ := m.povm_additive (⟨![imagTestEff i j hij, imagTestEff j i hji, C], hsumQ⟩ : POVM n 3)
  have hD := m.povm_additive (⟨![diagEffect i, diagEffect j, C], hsumD⟩ : POVM n 3)
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const] at hQ hD
  have hQ' : m.μ (imagTestEff i j hij) + m.μ (imagTestEff j i hji) + m.μ C = 1 := by
    simpa using hQ
  have hD' : m.μ (diagEffect i) + m.μ (diagEffect j) + m.μ C = 1 := by
    simpa using hD
  linarith [hQ', hD']

-- Step 3: Candidate ρ construction
private noncomputable def rhoCandidate {n : ℕ} (m : EffectMeasure n) : Op n :=
  Matrix.of fun i j =>
    if h : i = j then
      (m.μ (diagEffect i) : ℂ)
    else if i < j then
      ⟨m.μ (realTestEff i j h) - (m.μ (diagEffect i) + m.μ (diagEffect j)) / 2,
       (m.μ (diagEffect i) + m.μ (diagEffect j)) / 2 - m.μ (imagTestEff i j h)⟩
    else
      have hji : j ≠ i := fun hc => h hc.symm
      ⟨m.μ (realTestEff j i hji) - (m.μ (diagEffect j) + m.μ (diagEffect i)) / 2,
       -(((m.μ (diagEffect j) + m.μ (diagEffect i)) / 2 - m.μ (imagTestEff j i hji)))⟩

-- Step 4: ρ is Hermitian
private theorem rhoCandidate_hermitian {n : ℕ} (m : EffectMeasure n) :
    (rhoCandidate m).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, rhoCandidate, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij; simp [Complex.star_def]
  · simp only [hij, dif_neg]
    by_cases hlt : i < j
    · have hji_nlt : ¬(j < i) := not_lt.mpr (le_of_lt hlt)
      simp only [hlt, if_true, show ¬(j = i) from fun h => hij h.symm, dif_neg, hji_nlt, if_false]
      simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, neg_neg]
      apply Complex.ext <;> simp [add_comm]
    · have hji : j < i := by omega
      -- entry(j,i): j≠i, j<i → uses the i<j branch with j,i: ⟨re(j,i), im(j,i)⟩
      -- entry(i,j): i≠j, ¬(i<j) → uses the else branch: ⟨re(j,i), -im(j,i)⟩
      -- star(entry(j,i)) = conj(⟨r,q⟩) = ⟨r,-q⟩ should equal entry(i,j) = ⟨r,-q⟩ ✓
      simp only [hlt, if_false, show ¬(j = i) from fun h => hij h.symm, dif_neg, hji, if_true]
      simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, neg_neg]
      apply Complex.ext <;> simp [add_comm]

-- Step 5: Tr(ρ) = 1
private theorem rhoCandidate_trace_one {n : ℕ} (m : EffectMeasure n) :
    opTrace (rhoCandidate m) = 1 := by
  have hsum : (∑ i : Fin n, (diagEffect i).op) = 1 := diagEffects_sum_one n
  have hP := m.povm_additive (⟨diagEffect, hsum⟩ : POVM n n)
  simp only [opTrace, Matrix.trace, Matrix.diag, rhoCandidate, Matrix.of_apply, dif_pos rfl]
  -- Goal: ∑ i, (↑(m.μ (diagEffect i)) : ℂ) = 1
  have key : ∑ i : Fin n, m.μ (diagEffect i) = 1 := hP
  calc (∑ i : Fin n, (m.μ (diagEffect i) : ℂ))
      = ((∑ i : Fin n, m.μ (diagEffect i) : ℝ) : ℂ) := by push_cast; ring
    _ = ((1 : ℝ) : ℂ) := by rw [key]
    _ = 1 := by norm_cast

-- Step 6: ρ represents μ on test effects (by construction)
-- These are the inverse of the trace lemmas.

private lemma rhoCandidate_represents_diag {n : ℕ} (m : EffectMeasure n) (k : Fin n) :
    m.μ (diagEffect k) = (opTrace (rhoCandidate m * (diagEffect k).op)).re := by
  have : (diagEffect k).op = Matrix.single k k (1:ℂ) := rfl
  rw [this, trace_single_diag]
  simp only [rhoCandidate, Matrix.of_apply, dif_pos rfl]
  simp [Complex.ofReal_re]

private lemma rhoCandidate_represents_real_lt {n : ℕ} (m : EffectMeasure n)
    {i j : Fin n} (hij : i < j) :
    m.μ (realTestEff i j (ne_of_lt hij)) =
      (opTrace (rhoCandidate m * (realTestEff i j (ne_of_lt hij)).op)).re := by
  let hne : i ≠ j := ne_of_lt hij
  have htr := trace_realTestEff (rhoCandidate m) i j hne
  rw [htr]
  have hii : ((rhoCandidate m) i i).re = m.μ (diagEffect i) := by
    simp [rhoCandidate]
  have hjj : ((rhoCandidate m) j j).re = m.μ (diagEffect j) := by
    simp [rhoCandidate]
  have hij_re : ((rhoCandidate m) i j).re =
      m.μ (realTestEff i j hne) - (m.μ (diagEffect i) + m.μ (diagEffect j)) / 2 := by
    simp [rhoCandidate, hne, hij, not_lt.mpr (le_of_lt hij)]
  have hsym : (((rhoCandidate m) j i) + ((rhoCandidate m) i j)).re =
      2 * ((rhoCandidate m) i j).re := by
    simpa [add_comm] using hermitian_sym_re (rhoCandidate_hermitian m) i j
  have hsum :
      (((rhoCandidate m) i i) + ((rhoCandidate m) j i) + ((rhoCandidate m) i j) + ((rhoCandidate m) j j)).re =
      m.μ (diagEffect i) +
        2 * (m.μ (realTestEff i j hne) - (m.μ (diagEffect i) + m.μ (diagEffect j)) / 2) +
        m.μ (diagEffect j) := by
    calc
      (((rhoCandidate m) i i) + ((rhoCandidate m) j i) + ((rhoCandidate m) i j) + ((rhoCandidate m) j j)).re
          = (((rhoCandidate m) i i).re) + ((((rhoCandidate m) j i) + ((rhoCandidate m) i j)).re) +
              (((rhoCandidate m) j j).re) := by
              simp [Complex.add_re, add_assoc, add_left_comm, add_comm]
      _ = m.μ (diagEffect i) + 2 * ((rhoCandidate m) i j).re + m.μ (diagEffect j) := by
            rw [hii, hsym, hjj]
      _ = m.μ (diagEffect i) +
            2 * (m.μ (realTestEff i j hne) - (m.μ (diagEffect i) + m.μ (diagEffect j)) / 2) +
            m.μ (diagEffect j) := by rw [hij_re]
  have hhalf :
      (((1 / 2 : ℂ) *
          (((rhoCandidate m) i i) + ((rhoCandidate m) j i) + ((rhoCandidate m) i j) + ((rhoCandidate m) j j))).re)
      =
      (1 / 2 : ℝ) *
        ((((rhoCandidate m) i i) + ((rhoCandidate m) j i) + ((rhoCandidate m) i j) + ((rhoCandidate m) j j)).re) := by
    simp [Complex.mul_re]
  rw [hhalf, hsum]
  ring

private lemma rhoCandidate_represents_imag_lt {n : ℕ} (m : EffectMeasure n)
    {i j : Fin n} (hij : i < j) :
    m.μ (imagTestEff i j (ne_of_lt hij)) =
      (opTrace (rhoCandidate m * (imagTestEff i j (ne_of_lt hij)).op)).re := by
  let hne : i ≠ j := ne_of_lt hij
  have htr := trace_imagTestEff (rhoCandidate m) i j hne
  rw [htr]
  have hii : ((rhoCandidate m) i i).re = m.μ (diagEffect i) := by
    simp [rhoCandidate]
  have hjj : ((rhoCandidate m) j j).re = m.μ (diagEffect j) := by
    simp [rhoCandidate]
  have hij_im : ((rhoCandidate m) i j).im =
      (m.μ (diagEffect i) + m.μ (diagEffect j)) / 2 - m.μ (imagTestEff i j hne) := by
    simp [rhoCandidate, hne, hij, not_lt.mpr (le_of_lt hij)]
  have hanti : (-(Complex.I * ((rhoCandidate m) j i)) + Complex.I * ((rhoCandidate m) i j)).re =
      -2 * ((rhoCandidate m) i j).im := by
    simpa using hermitian_antisym_im (rhoCandidate_hermitian m) i j
  have hsum :
      (((rhoCandidate m) i i) + (-Complex.I) * ((rhoCandidate m) j i) + Complex.I * ((rhoCandidate m) i j) +
          ((rhoCandidate m) j j)).re =
      m.μ (diagEffect i) +
        (-2 * ((m.μ (diagEffect i) + m.μ (diagEffect j)) / 2 - m.μ (imagTestEff i j hne))) +
        m.μ (diagEffect j) := by
    calc
      (((rhoCandidate m) i i) + (-Complex.I) * ((rhoCandidate m) j i) + Complex.I * ((rhoCandidate m) i j) +
          ((rhoCandidate m) j j)).re
          = (((rhoCandidate m) i i).re) +
            ((-(Complex.I * ((rhoCandidate m) j i)) + Complex.I * ((rhoCandidate m) i j)).re) +
            (((rhoCandidate m) j j).re) := by
              simp [Complex.add_re, add_assoc, add_left_comm, add_comm]
      _ = m.μ (diagEffect i) + (-2 * ((rhoCandidate m) i j).im) + m.μ (diagEffect j) := by
            rw [hii, hanti, hjj]
      _ = m.μ (diagEffect i) +
            (-2 * ((m.μ (diagEffect i) + m.μ (diagEffect j)) / 2 - m.μ (imagTestEff i j hne))) +
            m.μ (diagEffect j) := by rw [hij_im]
  have hhalf :
      (((1 / 2 : ℂ) *
          (((rhoCandidate m) i i) + (-Complex.I) * ((rhoCandidate m) j i) + Complex.I * ((rhoCandidate m) i j) +
            ((rhoCandidate m) j j))).re)
      =
      (1 / 2 : ℝ) *
        ((((rhoCandidate m) i i) + (-Complex.I) * ((rhoCandidate m) j i) + Complex.I * ((rhoCandidate m) i j) +
          ((rhoCandidate m) j j)).re) := by
    simp [Complex.mul_re]
  rw [hhalf, hsum]
  ring

private lemma rhoCandidate_represents_real {n : ℕ} (m : EffectMeasure n)
    {i j : Fin n} (hij : i ≠ j) :
    m.μ (realTestEff i j hij) =
      (opTrace (rhoCandidate m * (realTestEff i j hij).op)).re := by
  by_cases hlt : i < j
  · have hltRep := rhoCandidate_represents_real_lt m hlt
    have hμ :
        m.μ (realTestEff i j hij) = m.μ (realTestEff i j (ne_of_lt hlt)) := by
      simpa using congrArg m.μ (realTestEff_proof_irrel i j hij (ne_of_lt hlt))
    have hop :
        (realTestEff i j hij).op = (realTestEff i j (ne_of_lt hlt)).op := by
      simpa using congrArg Effect.op (realTestEff_proof_irrel i j hij (ne_of_lt hlt))
    calc
      m.μ (realTestEff i j hij)
          = m.μ (realTestEff i j (ne_of_lt hlt)) := hμ
      _ = (opTrace (rhoCandidate m * (realTestEff i j (ne_of_lt hlt)).op)).re := hltRep
      _ = (opTrace (rhoCandidate m * (realTestEff i j hij).op)).re := by rw [hop]
  · have hji : j < i := by omega
    have hji_ne : j ≠ i := ne_of_lt hji
    have hltRep := rhoCandidate_represents_real_lt m hji
    have hswap : realTestEff i j hij = realTestEff j i hji_ne := realTestEff_swap i j hij hji_ne
    have hop :
        (realTestEff i j hij).op = (realTestEff j i hji_ne).op := by
      simpa [hswap] using congrArg Effect.op hswap
    calc
      m.μ (realTestEff i j hij)
          = m.μ (realTestEff j i hji_ne) := by rw [hswap]
      _ = (opTrace (rhoCandidate m * (realTestEff j i hji_ne).op)).re := hltRep
      _ = (opTrace (rhoCandidate m * (realTestEff i j hij).op)).re := by rw [hop]

private lemma rhoCandidate_trace_imag_pair_sum {n : ℕ} (m : EffectMeasure n)
    {i j : Fin n} (hij : i ≠ j) :
    (opTrace (rhoCandidate m * (imagTestEff i j hij).op)).re +
      (opTrace (rhoCandidate m * (imagTestEff j i (fun h => hij h.symm)).op)).re
      =
    (opTrace (rhoCandidate m * (diagEffect i).op)).re +
      (opTrace (rhoCandidate m * (diagEffect j).op)).re := by
  let hji : j ≠ i := fun h => hij h.symm
  calc
    (opTrace (rhoCandidate m * (imagTestEff i j hij).op)).re +
      (opTrace (rhoCandidate m * (imagTestEff j i hji).op)).re
        = (opTrace (rhoCandidate m * ((imagTestEff i j hij).op + (imagTestEff j i hji).op))).re := by
            rw [Matrix.mul_add, opTrace_add]
            simp [Complex.add_re]
    _ = (opTrace (rhoCandidate m * ((diagEffect i).op + (diagEffect j).op))).re := by
          rw [imagTestEff_pair_sum i j hij hji]
    _ = (opTrace (rhoCandidate m * (diagEffect i).op)).re +
          (opTrace (rhoCandidate m * (diagEffect j).op)).re := by
          rw [Matrix.mul_add, opTrace_add]
          simp [Complex.add_re]

private lemma rhoCandidate_represents_imag {n : ℕ} (m : EffectMeasure n)
    {i j : Fin n} (hij : i ≠ j) :
    m.μ (imagTestEff i j hij) =
      (opTrace (rhoCandidate m * (imagTestEff i j hij).op)).re := by
  by_cases hlt : i < j
  · have hltRep := rhoCandidate_represents_imag_lt m hlt
    have hμ :
        m.μ (imagTestEff i j hij) = m.μ (imagTestEff i j (ne_of_lt hlt)) := by
      simpa using congrArg m.μ (imagTestEff_proof_irrel i j hij (ne_of_lt hlt))
    have hop :
        (imagTestEff i j hij).op = (imagTestEff i j (ne_of_lt hlt)).op := by
      simpa using congrArg Effect.op (imagTestEff_proof_irrel i j hij (ne_of_lt hlt))
    calc
      m.μ (imagTestEff i j hij)
          = m.μ (imagTestEff i j (ne_of_lt hlt)) := hμ
      _ = (opTrace (rhoCandidate m * (imagTestEff i j (ne_of_lt hlt)).op)).re := hltRep
      _ = (opTrace (rhoCandidate m * (imagTestEff i j hij).op)).re := by rw [hop]
  · have hji : j < i := by omega
    have hji_ne : j ≠ i := ne_of_lt hji
    have hμpair := μ_imag_pair_sum m (i := i) (j := j) hij
    have hTrPair := rhoCandidate_trace_imag_pair_sum m (i := i) (j := j) hij
    have hDiagI := rhoCandidate_represents_diag m i
    have hDiagJ := rhoCandidate_represents_diag m j
    have hjiRep := rhoCandidate_represents_imag_lt m hji
    linarith [hμpair, hTrPair, hDiagI, hDiagJ, hjiRep]

private noncomputable def delta {n : ℕ} (m : EffectMeasure n) (E : Effect n) : ℝ :=
  m.μ E - (opTrace (rhoCandidate m * E.op)).re

private noncomputable def effectComplement {n : ℕ} (E : Effect n) : Effect n where
  op := 1 - E.op
  hermitian := E.bounded.1
  psd := E.bounded
  bounded := by
    have hpsd : IsPosSemidef (1 - (1 - E.op)) := by
      simpa [sub_sub_cancel] using E.psd
    simpa using hpsd

private lemma effectComplement_sum {n : ℕ} (E : Effect n) :
    E.op + (effectComplement E).op = 1 := by
  simp [effectComplement]

private lemma delta_diag {n : ℕ} (m : EffectMeasure n) (k : Fin n) :
    delta m (diagEffect k) = 0 := by
  unfold delta
  linarith [rhoCandidate_represents_diag m k]

private lemma delta_real {n : ℕ} (m : EffectMeasure n) {i j : Fin n} (hij : i ≠ j) :
    delta m (realTestEff i j hij) = 0 := by
  unfold delta
  linarith [rhoCandidate_represents_real m hij]

private lemma delta_imag {n : ℕ} (m : EffectMeasure n) {i j : Fin n} (hij : i ≠ j) :
    delta m (imagTestEff i j hij) = 0 := by
  unfold delta
  linarith [rhoCandidate_represents_imag m hij]

private lemma delta_binary_additivity {n : ℕ} (m : EffectMeasure n) (E F : Effect n)
    (h : IsPosSemidef (1 - (E.op + F.op))) :
    delta m (Effect.add E F h) = delta m E + delta m F := by
  unfold delta
  have hμ := binary_additivity m E F h
  have htr :
      (opTrace (rhoCandidate m * (Effect.add E F h).op)).re =
        (opTrace (rhoCandidate m * E.op)).re + (opTrace (rhoCandidate m * F.op)).re := by
    change (opTrace (rhoCandidate m * (E.op + F.op))).re =
      (opTrace (rhoCandidate m * E.op)).re + (opTrace (rhoCandidate m * F.op)).re
    rw [Matrix.mul_add, opTrace_add]
    simp [Complex.add_re]
  linarith [hμ, htr]

private lemma trace_povm_sum_one {n k : ℕ} (m : EffectMeasure n) (P : POVM n k) :
    ∑ i : Fin k, (opTrace (rhoCandidate m * (P.effects i).op)).re = 1 := by
  have hlin :
      opTrace (rhoCandidate m * (∑ i : Fin k, (P.effects i).op)) =
        ∑ i : Fin k, opTrace (rhoCandidate m * (P.effects i).op) := by
    change Matrix.trace (rhoCandidate m * (∑ i : Fin k, (P.effects i).op)) =
      ∑ i : Fin k, Matrix.trace (rhoCandidate m * (P.effects i).op)
    rw [Matrix.mul_sum, Matrix.trace_sum]
  have htrace :
      (opTrace (rhoCandidate m * (∑ i : Fin k, (P.effects i).op))).re = 1 := by
    rw [P.sum_eq_one, Matrix.mul_one, rhoCandidate_trace_one]
    norm_num
  have htrace' :
      (∑ i : Fin k, opTrace (rhoCandidate m * (P.effects i).op)).re = 1 := by
    rw [← hlin]
    exact htrace
  rw [Complex.re_sum] at htrace'
  simpa [add_comm, add_left_comm, add_assoc] using htrace'

private lemma delta_povm_sum_zero {n k : ℕ} (m : EffectMeasure n) (P : POVM n k) :
    ∑ i : Fin k, delta m (P.effects i) = 0 := by
  unfold delta
  rw [Finset.sum_sub_distrib]
  have hμ : (∑ i : Fin k, m.μ (P.effects i)) = 1 := m.povm_additive P
  have htr : (∑ i : Fin k, (opTrace (rhoCandidate m * (P.effects i).op)).re) = 1 :=
    trace_povm_sum_one m P
  linarith [hμ, htr]

private lemma delta_complement {n : ℕ} (m : EffectMeasure n) (E : Effect n) :
    delta m E + delta m (effectComplement E) = 0 := by
  have hsum : (∑ i : Fin 2, (![E, effectComplement E] i).op) = 1 := by
    simp [Fin.sum_univ_two, effectComplement_sum]
  have hδ := delta_povm_sum_zero m (⟨![E, effectComplement E], hsum⟩ : POVM n 2)
  simpa [Fin.sum_univ_two] using hδ

private lemma delta_one {n : ℕ} (m : EffectMeasure n) : delta m Effect.one = 0 := by
  unfold delta
  change m.μ Effect.one - (opTrace (rhoCandidate m * Effect.one.op)).re = 0
  rw [m.normalized]
  simp [Effect.one, rhoCandidate_trace_one]

private lemma delta_zero {n : ℕ} (m : EffectMeasure n) : delta m Effect.zero = 0 := by
  unfold delta
  rw [EffectMeasure.μ_zero m]
  change 0 - (opTrace (rhoCandidate m * Effect.zero.op)).re = 0
  simp [Effect.zero, opTrace]


-- Core Busch/Gleason linear extension: delta = 0 on all effects.
-- The proof uses: rhoCandidate was constructed so its entries match μ on test effects.
-- Since Re(Tr(·)) is linear and test effects span Herm(n), Re(Tr(rhoCandidate·E))
-- is determined by E's entries and μ-values. We show μ(E) equals this via POVM additivity.
-- The full proof requires ~150 lines of linear extension (rational homogeneity + boundedness
-- + 1D Jensen extension + spanning). This is the mathematical content of Busch/Gleason (1999/2003).
-- Reference: P. Busch, Phys. Rev. Lett. 91, 120403 (2003).
private lemma delta_eq_zero_core {n : ℕ} (m : EffectMeasure n) (E : Effect n) :
    delta m E = 0 := by
  sorry

private theorem rhoCandidate_represents {n : ℕ} (m : EffectMeasure n)
    (E : Effect n) : m.μ E = (opTrace (rhoCandidate m * E.op)).re := by
  have h := delta_eq_zero_core m E
  unfold delta at h; linarith

-- PSD follows from representation: for any v, the rank-1 projector |v><v|/||v||² is an effect,
-- and Re(<v, rho*v>) = ||v||² · μ(P_v) ≥ 0 by μ.nonneg.
-- The rank-1 projector construction requires ~80 lines (Hermitian, PSD, bounded proofs).
-- Reference: P. Busch, Phys. Rev. Lett. 91, 120403 (2003).
private theorem rhoCandidate_psd {n : ℕ} (m : EffectMeasure n) :
    IsPosSemidef (rhoCandidate m) := by
  exact ⟨rhoCandidate_hermitian m, fun v => by
    by_cases hv : v = 0
    · subst hv; simp [sesqForm]
    · sorry⟩

-- ============================================================
-- Main theorems
-- ============================================================

/-- **Busch/Gleason existence.**
Explicit construction: ρ is built entry-by-entry from μ via test effects.
- Hermitian: by construction (conjugate symmetry built in). PROVED.
- Tr(ρ)=1: from POVM additivity on diagEffects. PROVED.
- PSD: requires Busch/Gleason linear extension (1 sorry).
- Represents μ: requires Busch/Gleason linear extension (1 sorry).
Reference: P. Busch, Phys. Rev. Lett. 91, 120403 (2003). -/
theorem busch_gleason {n : ℕ} (m : EffectMeasure n) :
    ∃ ρ : DensityOp n, ∀ E : Effect n, m.μ E = (opTrace (ρ.ρ * E.op)).re :=
  ⟨⟨rhoCandidate m, rhoCandidate_hermitian m, rhoCandidate_psd m, rhoCandidate_trace_one m⟩,
   rhoCandidate_represents m⟩

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
