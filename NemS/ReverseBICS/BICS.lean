import NemS.Core.Basics
import NemS.Core.ObsEq
import NemS.Quantum.Effects
import NemS.Quantum.POVM
import NemS.Quantum.Measures
import NemS.Quantum.BuschGleason

/-!
# NemS.ReverseBICS.BICS

Born Internal & Complete Semantics (BICS): the definition and basic properties.

BICS is a semantic-architecture condition stating that quantum probability (Born rule)
provides the internal, context-independent, refinement-consistent, record-complete semantics
of the theory. It is NOT merely "Born rule holds as a frequency law"; it is a closure
condition on the semantic structure.

The reverse direction (Paper 14) proves: BICS ⇒ NEMS ⇒ PSC.
-/

namespace NemS
namespace ReverseBICS

open Quantum

/-- Born Internal & Complete Semantics (BICS).
A framework satisfies BICS if:
1. There exists an internal quantum state (density operator).
2. Record probabilities are given by the Born rule via a record-to-effect map.
3. Record semantics is noncontextual (context-independent).
4. No external completion bits: probability semantics is complete for record-truth.
-/
structure BICS (F : Framework) where
  /-- Dimension of the quantum Hilbert space. -/
  n : ℕ
  /-- Internal quantum state (density operator). -/
  ρ : DensityOp n
  /-- Mapping from record statements to quantum effects. -/
  recEff : F.Rec → Effect n
  /-- Record probability assignment. -/
  probTruth : F.Model → F.Rec → ℝ
  /-- Record probabilities are given internally by the Born rule. -/
  prob_is_born : ∀ (M : F.Model) (r : F.Rec),
      probTruth M r = (opTrace (ρ.ρ * (recEff r).op)).re
  /-- Noncontextuality: observationally equivalent records map to same effect. -/
  record_noncontextual : ∀ (r1 r2 : F.Rec),
      (∀ M, F.Truth M r1 ↔ F.Truth M r2) →
      recEff r1 = recEff r2
  /-- Completeness: probability semantics determines record-truth semantics.
  If two models agree on all record probabilities, they are observationally equivalent. -/
  no_external_completion_bits : ∀ (M1 M2 : F.Model),
      (∀ r, probTruth M1 r = probTruth M2 r) →
      F.ObsEq M1 M2

/-- If BICS holds, record probabilities are bounded in [0,1]. -/
theorem bics_prob_bounded {F : Framework} (h : BICS F) (M : F.Model) (r : F.Rec) :
    0 ≤ h.probTruth M r ∧ h.probTruth M r ≤ 1 := by
  rw [h.prob_is_born]
  set E := h.recEff r
  constructor
  · -- Re(Tr(ρE)) ≥ 0 for PSD ρ and effect E
    -- For PSD ρ and E: Re(Tr(ρE)) = Re(Σ_i Σ_j ρ_ij E_ji)
    -- = Re(Σ_i (ρE)_ii) = Σ_i Re((ρE)_ii)
    -- Each diagonal entry (ρE)_ii = Σ_j ρ_ij E_ji has nonneg real part
    -- because ρ, E are both PSD and Hermitian.
    -- The standard result: for PSD Hermitian A, B: Re(Tr(AB)) ≥ 0.
    -- Proof: write A = Σ_k λ_k |v_k><v_k| (spectral decomposition).
    -- Then Tr(AB) = Σ_k λ_k <v_k, B v_k>. Since B is PSD, <v_k, Bv_k> has nonneg real part.
    -- And λ_k ≥ 0. So Re(Tr(AB)) ≥ 0.
    -- In Lean: this requires spectral theory OR a direct sesqForm argument.
    -- For now: use the fact that ρ.psd and E.psd give the result.
    sorry
  · -- Re(Tr(ρE)) ≤ Tr(ρ) = 1 for effect E ≤ I
    have : opTrace (h.ρ.ρ * E.op) + opTrace (h.ρ.ρ * (1 - E.op)) = opTrace h.ρ.ρ := by
      change Matrix.trace (h.ρ.ρ * E.op) + Matrix.trace (h.ρ.ρ * (1 - E.op)) =
        Matrix.trace h.ρ.ρ
      rw [← Matrix.trace_add, ← Matrix.mul_add]
      simp [add_sub_cancel]
    have hre : (opTrace (h.ρ.ρ * E.op)).re + (opTrace (h.ρ.ρ * (1 - E.op))).re = 1 := by
      rw [← Complex.add_re, this, h.ρ.trace_one]; norm_num
    have hnn : 0 ≤ (opTrace (h.ρ.ρ * (1 - E.op))).re := by sorry  -- PSD of ρ and I-E
    linarith

/-- If BICS holds, the identity record (if it exists) has probability 1. -/
theorem bics_prob_one {F : Framework} (h : BICS F) (M : F.Model)
    (r_one : F.Rec) (hr_one : h.recEff r_one = Effect.one) :
    h.probTruth M r_one = 1 := by
  rw [h.prob_is_born, hr_one]
  simp [Effect.one, h.ρ.trace_one]

end ReverseBICS
end NemS

