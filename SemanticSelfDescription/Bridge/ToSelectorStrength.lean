import SemanticSelfDescription.Core.Claims
import SemanticSelfDescription.Core.SelfTheory
import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import SelectorStrength.Theorems.BarrierSchema
import SelectorStrength.Instances.Trivial

/-!
# SemanticSelfDescription.Bridge.ToSelectorStrength

**Bridge from final self-theory to SelectorStrength barrier.**

A final internal self-theory induces a total decider for self-semantic truth.
This reduction is the key step: the theorem statement is about semantic
self-description, but the proof reduces to the existing diagonal barrier.
-/

set_option autoImplicit false

namespace SemanticSelfDescription

universe u v

variable {W : Type u} (F : SelfSemanticFrame W)

/--
**Reduction**: A final self-theory yields a total decider for self-semantic truth.
The induced Bool predicate `theoryBoolPred T` decides `F.selfSemanticTruth`.
-/
theorem finalTheory_yields_totalDecider
    (T : InternalSelfTheory F) (hT : FinalSelfTheory T) :
    SelectorStrength.TotalDecider F.selfSemanticTruth (theoryBoolPred T) :=
  finalTheory_induces_totalDecider F T hT

/--
**DecidableAt reduction**: A final self-theory implies DecidableAt S_all
for self-semantic truth. This is the form needed to feed the barrier.
-/
theorem finalTheory_implies_decidableAt
    (T : InternalSelfTheory F) (hT : FinalSelfTheory T) :
    SelectorStrength.DecidableAt SelectorStrength.S_all F.selfSemanticTruth :=
  finalTheory_induces_decidableAt F T hT

end SemanticSelfDescription
