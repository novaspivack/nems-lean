import GPTClosure.Core.OrderedSpaces
import GPTClosure.Core.EffectsStates
import GPTClosure.Core.Measurements
import NemS.Quantum.MatrixBasics
import NemS.Quantum.Effects
import NemS.Quantum.POVM
import NemS.Quantum.Measures
import NemS.Quantum.BuschGleason
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Complex.Module

/-!
# GPTClosure.Instances.QuantumFinite

Quantum finite-dimensional instance of the GPT framework (Paper 39).

The space of n×n complex matrices `Op n`, viewed as a real vector space
via `Module.complexToReal`, carries a natural `OrderedUnitSpace` structure:
the PSD cone and identity as order unit. Density operators correspond to
GPT states, POVM elements to GPT effects, and the Born rule
`Pr_ρ(E) = Re(Tr(ρE))` matches the GPT probability `ω(e)`.

This module bridges the Paper 13 quantum formalization (NemS.Quantum)
with the Paper 39 GPT framework (GPTClosure), showing that quantum
probability is an instance of closure-forced probability.

## Proof status

- `quantumCone_pointed`: 1 sorry — pointedness of the PSD cone.
- `densityToState_nonneg`: 1 sorry — Re(Tr(ρA)) ≥ 0 for PSD ρ, A.
- `quantum_state_uniqueness`: 1 sorry — wiring to busch_gleason_unique
  (requires constructing an EffectMeasure with nonneg/le_one).

All structural definitions and the Born-rule-equals-GPT-pairing theorem
are fully proved.
-/

open NemS.Quantum

namespace GPTClosure.Instances.QuantumFinite

noncomputable section

variable {n : ℕ} [NeZero n]

-- ============================================================
-- Instance plumbing
-- ============================================================
-- Lean 4.29 / Mathlib v4.29 instance search cannot synthesize
-- Module ℝ (Op n) inside definition bodies when Op n appears as
-- a type argument to a structure with [Module ℝ V]. The abbrev
-- Op n = Matrix (Fin n) (Fin n) ℂ is not unfolded during instance
-- resolution in structure-constructor elaboration contexts.
-- We provide explicit named instances and thread them through all
-- GPTClosure structures via @ notation.

private def acgOp : AddCommGroup (Op n) := Matrix.addCommGroup
private def modROp : Module ℝ (Op n) :=
  @Module.complexToReal _ Matrix.addCommGroup Matrix.module

omit [NeZero n] in
private lemma smul_eq_complex_smul (c : ℝ) (A : Op n) :
    @HSMul.hSMul ℝ (Op n) (Op n) (@instHSMul ℝ (Op n) modROp.toSMul) c A =
    (↑c : ℂ) • A := rfl

omit [NeZero n] in
private lemma isHermitian_real_smul {A : Op n} (c : ℝ) (hA : A.IsHermitian) :
    ((↑c : ℂ) • A).IsHermitian := by
  unfold Matrix.IsHermitian at *
  rw [Matrix.conjTranspose_smul]
  simp [hA, Complex.conj_ofReal]

-- ============================================================
-- The PSD cone as a ConePredicate on Op n
-- ============================================================

/-- The PSD cone on Op n as a ConePredicate.

`pos_neg_iff_zero`: if A and −A are both PSD then A = 0. Standard
argument: for basis vector e_i, Re⟨e_i, A e_i⟩ ≥ 0 and
Re⟨e_i, (−A) e_i⟩ ≥ 0 force A_ii = 0; for e_i + e_j the
off-diagonal entries vanish similarly. -/
def quantumCone : @ConePredicate (Op n) acgOp modROp :=
  @ConePredicate.mk (Op n) acgOp modROp
    IsPosSemidef
    isPosSemidef_zero
    (fun _ _ hA hB => isPosSemidef_add hA hB)
    (fun c A hc hA => by
      change IsPosSemidef (@HSMul.hSMul ℝ (Op n) (Op n) (@instHSMul ℝ (Op n) modROp.toSMul) c A)
      rw [smul_eq_complex_smul]
      constructor
      · exact isHermitian_real_smul c hA.1
      · intro v
        simp only [sesqForm, Matrix.smul_apply, smul_eq_mul]
        rw [show (∑ i, ∑ j, starRingEnd ℂ (v i) * ((↑c : ℂ) * A i j) * v j) =
            (↑c : ℂ) * (∑ i, ∑ j, starRingEnd ℂ (v i) * A i j * v j) by
          simp only [Finset.mul_sum, mul_assoc, mul_left_comm]]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
        ring_nf
        exact mul_nonneg hc (hA.2 v))
    (fun _A _hA _hneg => by sorry)

-- ============================================================
-- The quantum ordered unit space
-- ============================================================

/-- The quantum ordered unit space: Op n with PSD cone and identity. -/
def quantumOUS : @OrderedUnitSpace (Op n) acgOp modROp :=
  @OrderedUnitSpace.mk (Op n) acgOp modROp
    quantumCone 1 isPosSemidef_one

-- ============================================================
-- Density operators → GPT states via the Born rule
-- ============================================================

/-- The Born rule linear map: E ↦ Re(Tr(ρE)).

This is ℝ-linear because opTrace is ℂ-linear, multiplication distributes,
and Re is ℝ-linear. The scalar action of ℝ on Op n factors through the
ℂ-scalar action via the embedding ℝ ↪ ℂ. -/
def bornMap (ρ : DensityOp n) :
    @LinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ) (Op n) ℝ
      acgOp.toAddCommMonoid (NonUnitalNonAssocSemiring.toAddCommMonoid)
      modROp (Semiring.toModule) :=
  @LinearMap.mk ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ) (Op n) ℝ
    acgOp.toAddCommMonoid (NonUnitalNonAssocSemiring.toAddCommMonoid)
    modROp (Semiring.toModule)
    { toFun := fun E => (opTrace (ρ.ρ * E)).re
      map_add' := fun E F => by
        change (opTrace (ρ.ρ * (E + F))).re = (opTrace (ρ.ρ * E)).re + (opTrace (ρ.ρ * F)).re
        simp only [Matrix.mul_add, opTrace_add, Complex.add_re] }
    (fun c E => by
      show (opTrace (ρ.ρ * (@HSMul.hSMul ℝ (Op n) (Op n) (@instHSMul ℝ (Op n) modROp.toSMul) c E))).re =
        (RingHom.id ℝ) c * (opTrace (ρ.ρ * E)).re
      rw [smul_eq_complex_smul, RingHom.id_apply]
      simp only [Matrix.mul_smul]
      rw [show opTrace ((↑c : ℂ) • (ρ.ρ * E)) = (↑c : ℂ) * opTrace (ρ.ρ * E) from by
        simp [opTrace, Matrix.trace, Matrix.diag, Finset.mul_sum]]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring)

/-- A density operator induces a GPT state via the Born rule.

`nonneg'`: Re(Tr(ρA)) ≥ 0 when both ρ and A are PSD. Standard proof:
write ρ = B*B via spectral decomposition, then Tr(ρA) = Tr(B*BA) =
Tr(AB*B) = ∑_i ⟨Be_i, A(Be_i)⟩ ≥ 0 since A is PSD. -/
def densityToState (ρ : DensityOp n) :
    @OrderedUnitSpace.State (Op n) acgOp modROp quantumOUS :=
  @OrderedUnitSpace.State.mk (Op n) acgOp modROp quantumOUS
    (bornMap ρ)
    (fun _A _hA => by sorry)
    (by show (opTrace (ρ.ρ * 1)).re = 1
        rw [Matrix.mul_one]
        have h := ρ.trace_one
        rw [opTrace] at h ⊢
        exact_mod_cast congr_arg Complex.re h)

-- ============================================================
-- Quantum effects → GPT effects
-- ============================================================

/-- A quantum effect (Paper 13) corresponds to a GPT effect (Paper 39).
    0 ≤ E ≤ I in the Loewner order matches the GPT cone ordering. -/
def quantumEffectToGPT (E : NemS.Quantum.Effect n) :
    @OrderedUnitSpace.Effect (Op n) acgOp modROp quantumOUS := by
  refine ⟨E.op, ?_, ?_⟩
  · -- 0 ≤ E.op, i.e., quantumCone.Pos (E.op - 0) = IsPosSemidef (E.op - 0)
    change IsPosSemidef (E.op - 0)
    convert E.psd
    exact sub_zero E.op
  · -- E.op ≤ 1, i.e., quantumCone.Pos (1 - E.op) = IsPosSemidef (1 - E.op)
    change IsPosSemidef (1 - E.op)
    exact E.bounded

-- ============================================================
-- The Born rule = GPT state-effect pairing
-- ============================================================

/-- The Born rule probability Re(Tr(ρE)) matches the GPT state-effect pairing.
    This is the key theorem: quantum probability IS GPT probability. -/
omit [NeZero n] in
theorem born_rule_is_gpt_prob (ρ : DensityOp n) (E : NemS.Quantum.Effect n) :
    @OrderedUnitSpace.stateEffectProb (Op n) acgOp modROp quantumOUS
      (densityToState ρ) (quantumEffectToGPT E) =
      (opTrace (ρ.ρ * E.op)).re := rfl

-- ============================================================
-- POVM → GPT measurement
-- ============================================================

/-- A quantum POVM (Paper 13) corresponds to a GPT measurement (Paper 39). -/
def povmToMeasurement {k : ℕ} (P : POVM n k) :
    @OrderedUnitSpace.Measurement (Op n) acgOp modROp quantumOUS k :=
  @OrderedUnitSpace.Measurement.mk (Op n) acgOp modROp quantumOUS k
    (fun i => quantumEffectToGPT (P.effects i))
    P.sum_eq_one

-- ============================================================
-- Uniqueness: Busch/Gleason ↔ GPT state extensionality
-- ============================================================

/-- The Busch/Gleason uniqueness theorem (Paper 13) implies GPT state
    uniqueness (Paper 39): if two density operators give the same Born
    probabilities on all effects, they must be equal.

    This is the quantum instance of `state_ext_effect_span`. -/
theorem quantum_state_uniqueness (ρ₁ ρ₂ : DensityOp n)
    (h : ∀ E : NemS.Quantum.Effect n,
      (opTrace (ρ₁.ρ * E.op)).re = (opTrace (ρ₂.ρ * E.op)).re) :
    ρ₁.ρ = ρ₂.ρ := by
  sorry

end

end GPTClosure.Instances.QuantumFinite
