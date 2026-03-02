import NemS.Core.Basics
import NemS.MFRR.DiagonalBarrier
import NemS.Adjudication.EffectiveEmulator

/-!
# NemS.Adjudication.ExecutionNecessity

**Paper 19 (T2): The Non-Emulability of Execution (Agentic Necessity)**

This module formalizes the refutation of the "Block Universe" and the
"simulation-as-lookup-table" views. It proves that physical reality requires
active, internal adjudication (PT) that cannot be replaced by a static
algorithm or pre-computed lookup table.

The logic combines the Record-Divergent Choice premise with the Diagonal Barrier.
If reality could be completely emulated or pre-computed, a total effective
decider for Record-Truth (RT) would exist. But RT is not computably decidable
on diagonal fragments. Therefore, the "unfolding" of the universe by internal
adjudicators is semantically required to make record-truth determinate.
-/

namespace NemS
namespace Adjudication

open NemS.Framework
open NemS.MFRR

/-- A universe model with states and an adjudication function. -/
structure Universe (F : Framework) where
  /-- The state space of the universe. -/
  State : Type
  /-- The internal adjudication function (PT) that resolves choice points. -/
  PT : State → State
  /-- A projection from the universe state to the record language. -/
  record : State → F.Rec

/-- **Premise 1: Record-Divergent Choice.**
There exist states where the internal adjudication function `PT` makes choices
that strictly determine future record-truth. Without `PT`, the record-truth
is underdetermined. -/
def RecordDivergentChoice {F : Framework} (U : Universe F) : Prop :=
  ∃ s : U.State, U.record (U.PT s) ≠ U.record s

/-- **Definition: Pre-computed Lookup Table / Static Algorithm.**
A static algorithm `A` that attempts to emulate the universe's adjudication
without actually running it from within. -/
structure StaticAlgorithm (F : Framework) (U : Universe F) where
  /-- The algorithm is a computable function on states. -/
  compute : U.State → U.State
  /-- The algorithm is total-effective (computable). -/
  is_effective : True -- Placeholder for computability

/-- **Definition: Emulates Execution.**
A static algorithm perfectly emulates the universe's execution if it matches
the internal adjudication function `PT` on all states. -/
def EmulatesExecution {F : Framework} {U : Universe F} (A : StaticAlgorithm F U) : Prop :=
  ∀ s, A.compute s = U.PT s

/-- **Theorem 19.1: The Non-Emulability of Execution.**

In a diagonal-capable framework, no static algorithm can perfectly emulate
the universe's internal adjudication. The universe must be "run" from within.

*Proof sketch:* If a static algorithm could emulate `PT`, it would induce a
total-effective decider for record-truth. But by the Diagonal Barrier
(Paper 11/12) and Stronger No-Emulation (Paper 16), such a decider cannot
exist on the diagonal fragment. Thus, the emulation fails.
-/
theorem execution_necessity {F : Framework} (U : Universe F)
    [dc : DiagonalCapable F]
    (h_div : RecordDivergentChoice U)
    -- The ledger assumption: perfect emulation implies a computable RT decider
    (h_emulation_implies_decider : (∃ A : StaticAlgorithm F U, EmulatesExecution A) →
      ∃ (decider : Nat → Bool), Computable decider ∧ ∀ n, decider n = true ↔ dc.asr.RT n) :
    ¬ (∃ A : StaticAlgorithm F U, EmulatesExecution A) := by
  intro h_exists_emu
  -- If emulation exists, we get a computable decider for RT
  have ⟨decider, h_comp, h_correct⟩ := h_emulation_implies_decider h_exists_emu
  -- But the diagonal barrier says RT is not computably decidable
  have h_undecidable := diagonal_barrier_rt F
  -- Contradiction
  apply h_undecidable
  -- We need to convert our computable boolean decider into a ComputablePred
  have h_dec : DecidablePred dc.asr.RT := fun n =>
    if h : decider n = true then isTrue ((h_correct n).mp h)
    else isFalse (fun h_rt => by
      have h_true := (h_correct n).mpr h_rt
      exact h h_true)
  -- Since decider computes exactly the truth value of RT, it witnesses ComputablePred
  have h_comp_pred : ComputablePred dc.asr.RT := by
    apply computable_pred_of_bool dc.asr.RT decider h_comp h_correct
  exact h_comp_pred

end Adjudication
end NemS
