import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.Spectrum

/-!
# NemS.Quantum.MatrixBasics

Basic definitions for quantum operators on ℂ^n.

We work with `Matrix (Fin n) (Fin n) ℂ` throughout.
Since `ℂ` has no `PartialOrder`, we define positive semidefiniteness
directly via the sesquilinear form: A is PSD if A is Hermitian and
∀ v, Re(⟨v, Av⟩) ≥ 0, where ⟨v, w⟩ = ∑ i, conj(v i) * w i.
-/

namespace NemS
namespace Quantum

/-- Operator on n-dimensional complex Hilbert space. -/
abbrev Op (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Trace of an operator. -/
noncomputable def opTrace {n : ℕ} (A : Op n) : ℂ := Matrix.trace A

/-- The sesquilinear form: ⟨v, Av⟩ = ∑ i j, conj(v i) * A i j * v j -/
noncomputable def sesqForm {n : ℕ} (A : Op n) (v : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ (v i)) * A i j * v j

/-- A is positive semidefinite: Hermitian and ∀ v, Re(⟨v, Av⟩) ≥ 0. -/
def IsPosSemidef {n : ℕ} (A : Op n) : Prop :=
  A.IsHermitian ∧ ∀ v : Fin n → ℂ, (0 : ℝ) ≤ (sesqForm A v).re

/-- The zero operator is PSD. -/
theorem isPosSemidef_zero {n : ℕ} : IsPosSemidef (0 : Op n) := by
  constructor
  · exact Matrix.isHermitian_zero
  · intro v; simp [sesqForm]

/-- The identity operator is PSD. Proof: Re(⟨v, Iv⟩) = ∑ᵢ|vᵢ|² ≥ 0. -/
theorem isPosSemidef_one {n : ℕ} : IsPosSemidef (1 : Op n) :=
  ⟨Matrix.isHermitian_one, fun v => by
    simp only [sesqForm, Matrix.one_apply]
    -- Reduce double sum to diagonal
    have step : (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (v i) * (if i = j then 1 else 0) * v j)
        = ∑ i : Fin n, starRingEnd ℂ (v i) * v i := by
      congr 1; ext i
      simp [Finset.mem_univ]
    rw [step]
    -- Re(∑ᵢ conj(vᵢ)·vᵢ) = ∑ᵢ Re(conj(vᵢ)·vᵢ) = ∑ᵢ |vᵢ|² ≥ 0
    rw [show (∑ i : Fin n, starRingEnd ℂ (v i) * v i).re =
        ∑ i : Fin n, (starRingEnd ℂ (v i) * v i).re from by simp [Complex.re_sum]]
    apply Finset.sum_nonneg
    intro i _
    -- (starRingEnd ℂ (v i) * v i).re = vᵢ.re² + vᵢ.im² ≥ 0
    have : (starRingEnd ℂ (v i) * v i).re = (v i).re * (v i).re + (v i).im * (v i).im := by
      simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    rw [this]
    nlinarith [sq_nonneg (v i).re, sq_nonneg (v i).im]⟩

/-- Sum of PSD operators is PSD. Proof: Re is linear. -/
theorem isPosSemidef_add {n : ℕ} {A B : Op n}
    (hA : IsPosSemidef A) (hB : IsPosSemidef B) : IsPosSemidef (A + B) :=
  ⟨hA.1.add hB.1, fun v => by
    have h1 := hA.2 v; have h2 := hB.2 v
    simp only [sesqForm, Matrix.add_apply] at *
    have split : (∑ i, ∑ j, starRingEnd ℂ (v i) * (A i j + B i j) * v j).re =
        (∑ i, ∑ j, starRingEnd ℂ (v i) * A i j * v j).re +
        (∑ i, ∑ j, starRingEnd ℂ (v i) * B i j * v j).re := by
      rw [show (∑ i, ∑ j, starRingEnd ℂ (v i) * (A i j + B i j) * v j) =
          (∑ i, ∑ j, starRingEnd ℂ (v i) * A i j * v j) +
          (∑ i, ∑ j, starRingEnd ℂ (v i) * B i j * v j) by
        simp only [mul_add, add_mul, Finset.sum_add_distrib]]
      exact Complex.add_re _ _
    linarith [split]⟩

/-- Trace is additive. -/
theorem opTrace_add {n : ℕ} (A B : Op n) :
    opTrace (A + B) = opTrace A + opTrace B :=
  Matrix.trace_add A B

/-- Trace is cyclic. -/
theorem opTrace_mul_comm {n : ℕ} (A B : Op n) :
    opTrace (A * B) = opTrace (B * A) :=
  Matrix.trace_mul_comm A B

/-- The Loewner order: A ≤ B means B - A is PSD. -/
def loewnerLE {n : ℕ} (A B : Op n) : Prop := IsPosSemidef (B - A)

end Quantum
end NemS
