import SemanticSelfDescription.Core.Claims
import SemanticSelfDescription.Theorems.NoFinalSelfTheory
import SemanticSelfDescription.Bridge.ToLearning
import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders

/-!
# SemanticSelfDescription.Bridge.ToSelfAwareness

**Bridge: Necessary Incompleteness implies selector necessity (Paper 33).**

When a SelfSemanticFrame satisfies BarrierHypotheses, the selection-among-
fixed-points barrier (SelfAwareness, Paper 33) holds: selection cannot be
total-effective. Immediate from the Learning bridge (ToLearning).
-/

set_option autoImplicit false

namespace SemanticSelfDescription

universe u v

variable {W : Type u} (F : SelfSemanticFrame W)

/--
**Selector necessity under barrier hypotheses.**

When the frame satisfies BarrierHypotheses, selection among indistinguishable
fixed points cannot be total-effective (SelfAwareness, Paper 33). Same barrier
as no_final_self_theory and no_total_decider_under_barrier.
-/
theorem selector_necessity_under_barrier (hB : BarrierHypotheses F) :
    ¬ SelectorStrength.DecidableAt SelectorStrength.S_all F.selfSemanticTruth :=
  no_total_decider_under_barrier F hB

end SemanticSelfDescription
