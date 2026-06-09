import NemS.Diagonal.HaltingReduction

/-!
# NemS.Diagonal.NoConvergenceModulus

Theorem C (operational no-hypercomputation): no total computable modulus
stabilizes a stage approximation of record-truth. A computable modulus
would make `RT` computably decidable, contradicting the diagonal barrier.
-/

namespace NemS
namespace Diagonal

variable {F : Framework}

/-- A total computable stage approximation to a predicate with a
total computable convergence modulus. -/
structure ComputableConvergenceModulus (p : ℕ → Prop) [DecidablePred p] where
  /-- Stage approximation `g n s` decides `p n` once `s` exceeds the modulus. -/
  g : ℕ → ℕ → Bool
  g_computable : Computable₂ g
  /-- Total computable modulus `s₀ n`. -/
  s₀ : ℕ → ℕ
  s₀_computable : Computable s₀
  /-- Beyond the modulus, the stage function is stable at the truth value. -/
  stable : ∀ n, ∀ s ≥ s₀ n, g n s = decide (p n)

/-- A computable convergence modulus yields a computable decider for `p`. -/
theorem computableConvergenceModulus_implies_computablePred
    {p : ℕ → Prop} [DecidablePred p]
    (m : ComputableConvergenceModulus p) : ComputablePred p := by
  refine ⟨inferInstance, ?_⟩
  have h : ∀ n, decide (p n) = m.g n (m.s₀ n) := fun n =>
    (m.stable n (m.s₀ n) le_rfl).symm
  simpa [h] using m.g_computable.comp Computable.id m.s₀_computable

/-- **No computable convergence modulus for record-truth (Theorem C).**

If a total computable stage function with a total computable modulus
decides `RT` beyond the modulus, then `RT` is computably decidable —
contradicting `asr_rt_not_computable`. -/
theorem no_computable_convergence_modulus
    (asr : ASR F) {p : ℕ → Prop} [DecidablePred p]
    (hEq : ∀ n, p n ↔ asr.RT n) :
    ¬ ∃ m : ComputableConvergenceModulus p, True := by
  classical
  rintro ⟨m, _⟩
  have inst : ∀ n, Decidable (asr.RT n) := fun n => decidable_of_iff _ (hEq n)
  letI : DecidablePred asr.RT := inst
  have hRT : ComputablePred asr.RT :=
    (computableConvergenceModulus_implies_computablePred m).of_eq hEq
  exact asr_rt_not_computable asr hRT

/-- Corollary for `RT` itself. -/
theorem no_computable_convergence_modulus_RT
    (asr : ASR F) [DecidablePred asr.RT] :
    ¬ ∃ _m : ComputableConvergenceModulus asr.RT, True :=
  no_computable_convergence_modulus asr (fun _ => Iff.rfl)

end Diagonal
end NemS
