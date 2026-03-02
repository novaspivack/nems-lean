import NemS.Core.Basics
import NemS.MFRR.DiagonalBarrier
import NemS.Adjudication.EffectiveEmulator

/-!
# NemS.Adjudication.ExecutionNecessity

**Paper 19 (T2): The Non-Emulability of Execution (Agentic Necessity)**

This module formalizes the refutation of the "simulation-as-lookup-table" view.
It proves that physical reality requires active, internal adjudication (PT)
that cannot be replaced by a static algorithm or pre-computed lookup table.

The logic relies on the Instance Encoding machinery from Paper 16. If reality
could be completely emulated by a static algorithm that is total-effective on
diagonal instances, a computable decider for Record-Truth (RT) would exist.
But RT is not computably decidable on diagonal fragments. Therefore, the
"unfolding" of the universe by internal adjudicators is semantically required
to make record-truth determinate.
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

/-- **Premise (L19.1'): Instance Encoding for RT.**
There exists a computable map from codes to states, and a computable extraction
from states to a boolean deciding RT. This is exactly the `InstanceEncoding`
from Paper 16, adapted for the Universe state space. -/
structure UniverseInstanceEncoding {F : Framework} (U : Universe F) (dc : DiagonalCapable F) where
  diagInstance : Nat → U.State
  extract_RT : U.State → Bool
  correctness : ∀ n, extract_RT (U.PT (diagInstance n)) = true ↔ dc.asr.RT n

/-- **Definition: Static Algorithm.**
A static algorithm `A` that attempts to emulate the universe's adjudication. -/
structure StaticAlgorithm (F : Framework) (U : Universe F) where
  compute : U.State → U.State

/-- **Definition: Effective on Diagonal Instances.**
An algorithm is effective on diagonal instances if the composition of
instance preparation, computation, and extraction is computable. -/
def IsEffectiveOnDiagonal {F : Framework} {U : Universe F} {dc : DiagonalCapable F}
    (enc : UniverseInstanceEncoding U dc) (A : StaticAlgorithm F U) : Prop :=
  Computable (fun n => enc.extract_RT (A.compute (enc.diagInstance n)))

/-- **Definition: Emulates Execution on Diagonal Instances.**
A static algorithm emulates the universe's execution on diagonal instances if
it matches the internal adjudication function `PT` on those states. -/
def EmulatesExecutionOnDiagonal {F : Framework} {U : Universe F} {dc : DiagonalCapable F}
    (enc : UniverseInstanceEncoding U dc) (A : StaticAlgorithm F U) : Prop :=
  ∀ n, A.compute (enc.diagInstance n) = U.PT (enc.diagInstance n)

/-- **Theorem 19.1: The Non-Emulability of Execution.**

In a diagonal-capable framework, no static algorithm can both emulate the
universe's internal adjudication on diagonal instances and be total-effective
on those instances. The universe must be "run" from within.
-/
theorem execution_necessity {F : Framework} (U : Universe F)
    [dc : DiagonalCapable F]
    (enc : UniverseInstanceEncoding U dc) :
    ¬ (∃ A : StaticAlgorithm F U,
        EmulatesExecutionOnDiagonal enc A ∧ IsEffectiveOnDiagonal enc A) := by
  intro h_exists
  rcases h_exists with ⟨A, h_emulates, h_effective⟩
  
  -- Construct the decider
  let decider := fun n => enc.extract_RT (A.compute (enc.diagInstance n))
  
  -- The decider is computable by assumption
  have h_comp : Computable decider := h_effective
  
  -- The decider is correct because A emulates PT on diagonal instances
  have h_correct : ∀ n, decider n = true ↔ dc.asr.RT n := by
    intro n
    have h_eq : A.compute (enc.diagInstance n) = U.PT (enc.diagInstance n) := h_emulates n
    -- We need to unfold decider to substitute
    have h_dec_eq : decider n = enc.extract_RT (A.compute (enc.diagInstance n)) := rfl
    rw [h_dec_eq, h_eq]
    exact enc.correctness n

  -- Convert the boolean decider into a ComputablePred
  have h_comp_pred : ComputablePred dc.asr.RT := by
    apply computable_pred_of_bool dc.asr.RT decider h_comp h_correct

  -- Contradict the diagonal barrier
  exact diagonal_barrier_rt F h_comp_pred

end Adjudication
end NemS
