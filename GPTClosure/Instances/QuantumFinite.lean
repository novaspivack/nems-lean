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
    (fun A hA hNeg => by
      -- Pointed cone: A PSD and -A PSD implies A = 0.
      -- Proof: Re(sesqForm A v) ≥ 0 (from hA) and Re(sesqForm (-A) v) ≥ 0 (from hNeg)
      -- gives ∀ v, Re(sesqForm A v) = 0. Then A = 0 by basis evaluation + Hermitian.
      -- STEP 1: ∀ v, Re(sesqForm A v) = 0.
      have hzero : ∀ v : Fin n → ℂ, (sesqForm A v).re = 0 := fun v => by
        have h1 : 0 ≤ (sesqForm A v).re := hA.2 v
        have h2 : 0 ≤ (sesqForm (-A) v).re := hNeg.2 v
        have h2' : (sesqForm A v).re ≤ 0 := by
          have : (sesqForm (-A) v).re = -(sesqForm A v).re := by
            simp [sesqForm, Finset.sum_neg_distrib, mul_neg, Complex.neg_re]
          linarith [this ▸ h2]
        linarith
      -- STEP 2: For each basis vector eᵢ, sesqForm A eᵢ = Aᵢᵢ (diagonal entry).
      -- And Aᵢᵢ is real (Hermitian). So Aᵢᵢ.re = 0 and Aᵢᵢ.im = 0, giving Aᵢᵢ = 0.
      -- STEP 3: For off-diagonal: sesqForm A (eᵢ + eⱼ).re = Aᵢᵢ.re + Aⱼⱼ.re + 2*Re(Aᵢⱼ)
      --         = 2*Re(Aᵢⱼ) = 0. Similarly Im via eᵢ + i*eⱼ.
      -- LEAN PROOF via Tr(A²) = 0 (cleaner for Lean):
      -- For PSD A: Re(Tr(A*A)) ≥ 0 via axiom re_trace_psd_mul_psd_nonneg.
      -- For PSD -A: Re(Tr((-A)*A)) ≥ 0. But Tr((-A)*A) = -Tr(A²), so Re(Tr(A²)) ≤ 0.
      -- So Tr(A²) has Re = 0. For Hermitian A: (A*A)ᵢᵢ = ∑ⱼ Aᵢⱼ * Aⱼᵢ = ∑ⱼ |Aᵢⱼ|².
      -- All |Aᵢⱼ|² ≥ 0 and sum of Re((A*A)ᵢᵢ) = 0, so each |Aᵢⱼ|² = 0, so Aᵢⱼ = 0.
      have hA2_re_zero : (opTrace (A * A)).re = 0 := by
        have hnn : (0 : ℝ) ≤ (opTrace (A * A)).re :=
          re_trace_psd_mul_psd_nonneg hA hA
        have hnn2 : (0 : ℝ) ≤ (opTrace ((-A) * A)).re :=
          re_trace_psd_mul_psd_nonneg hNeg hA
        have : (opTrace ((-A) * A)).re = -(opTrace (A * A)).re := by
          simp [opTrace, Matrix.trace_neg, neg_mul]
        linarith [this ▸ hnn2]
      -- From Re(Tr(A²)) = 0, extract each entry = 0.
      apply Matrix.ext; intro i j
      -- (A*A)ᵢⱼ = ∑ₖ Aᵢₖ Aₖⱼ. For Hermitian A: Aₖⱼ = conj(Aⱼₖ).
      -- Diagonal (A*A)ᵢᵢ = ∑ₖ Aᵢₖ * conj(Aᵢₖ) = ∑ₖ |Aᵢₖ|² ≥ 0.
      -- Re(Tr(A²)) = ∑ᵢ Re((A²)ᵢᵢ) = ∑ᵢ ∑ₖ |Aᵢₖ|² = 0.
      -- So ∀ i k, |Aᵢₖ|² = 0, so Aᵢₖ = 0.
      -- We show Aᵢⱼ = 0 via: |Aᵢⱼ|² ≤ Re(Tr(A²)) = 0.
      -- Actually |Aᵢⱼ|² ≤ (A*A)ᵢᵢ (diagonal dominance for PSD) then ≤ Tr(A²) = 0.
      -- Lean proof: via Finset.sum_eq_zero and nonneg contribution.
      have h_entry_sq : Complex.normSq (A i j) = 0 := by
        have h_bound : Complex.normSq (A i j) ≤ (opTrace (A * A)).re := by
          -- |Aᵢⱼ|² is one term in the sum ∑ᵢ ∑ₖ |Aᵢₖ|².
          -- Re(Tr(A²)) = ∑ᵢ ∑ₖ Re(Aᵢₖ * Aₖᵢ) = ∑ᵢ ∑ₖ Re(Aᵢₖ * conj(Aᵢₖ)) = ∑ᵢ ∑ₖ |Aᵢₖ|².
          -- Each term is nonneg, so |Aᵢⱼ|² ≤ total sum.
          simp only [opTrace, Matrix.trace, Matrix.diag, Matrix.mul_apply]
          rw [show (∑ x : Fin n, (∑ x_1 : Fin n, A x x_1 * A x_1 x)).re =
              ∑ p : Fin n, ∑ q : Fin n, (A p q * A q p).re from by
            simp [Complex.re_sum]]
          apply Finset.single_le_sum (fun p _ => Finset.sum_nonneg (fun q _ => by
            -- (A p q * A q p).re ≥ 0 since A q p = conj(A p q) (Hermitian)
            have := hA.1.apply p q
            simp only [Matrix.IsHermitian, Matrix.conjTranspose_apply] at hA
            have hconjpq : A q p = starRingEnd ℂ (A p q) := by
              have := congr_fun (congr_fun hA.1 q) p
              simp [Matrix.conjTranspose_apply, starRingEnd] at this
              exact this.symm
            rw [hconjpq]
            simp [Complex.normSq_apply, Complex.mul_re, Complex.star_def,
                  Complex.conj_re, Complex.conj_im]
            nlinarith [sq_nonneg (A p q).re, sq_nonneg (A p q).im]))
            (Finset.mem_univ i) _ (Finset.mem_univ j)
          -- Individual term at (i, j):
          have hconjij : A j i = starRingEnd ℂ (A i j) := by
            have := congr_fun (congr_fun hA.1 j) i
            simp [Matrix.conjTranspose_apply, starRingEnd] at this
            exact this.symm
          rw [hconjij]
          simp [Complex.normSq_apply, Complex.mul_re, Complex.star_def,
                Complex.conj_re, Complex.conj_im]
        have hnn : 0 ≤ Complex.normSq (A i j) := Complex.normSq_nonneg _
        linarith [hA2_re_zero ▸ h_bound]
      -- From normSq = 0, conclude A i j = 0.
      exact Complex.normSq_eq_zero.mp h_entry_sq

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
    (fun A hA => re_trace_psd_mul_psd_nonneg ρ.psd hA)
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
  -- Build an EffectMeasure from ρ₁ and apply busch_gleason_unique.
  -- μ(E) = Re(Tr(ρ₁.ρ * E.op)) satisfies: normalized (Tr(ρ)=1), POVM additive, nonneg, le_one.
  let m : EffectMeasure n := {
    μ := fun E => (opTrace (ρ₁.ρ * E.op)).re
    normalized := by
      simp [opTrace, Effect.one, Matrix.mul_one]
      exact_mod_cast ρ₁.trace_one
    povm_additive := by
      intro k P
      have : ∑ i, opTrace (ρ₁.ρ * (P.effects i).op) = opTrace (ρ₁.ρ * 1) := by
        rw [← Matrix.mul_sum]
        congr 1
        have := P.sum_eq_one
        simp only [Matrix.sum_apply] at this ⊢
        ext i j
        simp [Finset.sum_apply, this]
      have hre : (∑ i, opTrace (ρ₁.ρ * (P.effects i).op)).re = 1 := by
        rw [this]
        simp [opTrace, Matrix.mul_one]
        exact_mod_cast ρ₁.trace_one
      simp only [Complex.re_sum] at hre
      exact hre
    nonneg := fun E => re_trace_psd_mul_psd_nonneg ρ₁.psd E.psd
    le_one := by
      intro E
      have hbound : (opTrace (ρ₁.ρ * E.op)).re + (opTrace (ρ₁.ρ * (1 - E.op))).re = 1 := by
        have hsum : opTrace (ρ₁.ρ * E.op) + opTrace (ρ₁.ρ * (1 - E.op)) = opTrace ρ₁.ρ := by
          rw [← Matrix.mul_add]; simp [opTrace]
        have : (opTrace (ρ₁.ρ * E.op) + opTrace (ρ₁.ρ * (1 - E.op))).re = 1 := by
          rw [hsum]; simp [opTrace]; exact_mod_cast ρ₁.trace_one
        simp [Complex.add_re] at this; exact this
      have hnn : 0 ≤ (opTrace (ρ₁.ρ * (1 - E.op))).re :=
        re_trace_psd_mul_psd_nonneg ρ₁.psd E.bounded
      linarith
  }
  -- Apply busch_gleason_unique: both ρ₁ and ρ₂ represent m.
  apply busch_gleason_unique m ρ₁ ρ₂
  · intro E; rfl
  · intro E; exact (h E).symm

end

end GPTClosure.Instances.QuantumFinite
