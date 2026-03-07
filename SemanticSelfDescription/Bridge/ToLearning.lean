import SemanticSelfDescription.Core.Claims
import SemanticSelfDescription.Theorems.NoFinalSelfTheory
import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import SelectorStrength.Instances.Trivial

/-!
# SemanticSelfDescription.Bridge.ToLearning

**Bridge: Necessary Incompleteness implies no total self-certifier (Paper 30).**

When a SelfSemanticFrame satisfies BarrierHypotheses, the same diagonal barrier
that rules out a final internal self-theory also rules out a total internal
self-certifier (Learning, Paper 30). Both reduce to SelectorStrength. We prove
the Learning formulation directly from our setup.
-/

set_option autoImplicit false

namespace SemanticSelfDescription

universe u v

variable {W : Type u} (F : SelfSemanticFrame W)

/--
**No total decider under barrier hypotheses (Learning formulation).**

When the frame satisfies BarrierHypotheses, there is no total decider for
self-semantic truth at strength S_all. This is the same barrier that Learning
(Paper 30) states as "no total self-certifier" when certificates = codes.
-/
theorem no_total_decider_under_barrier (hB : BarrierHypotheses F) :
    ¬ SelectorStrength.DecidableAt SelectorStrength.S_all F.selfSemanticTruth :=
  SelectorStrength.no_total_decider_all hB.codeExt.CodeEquiv F.selfSemanticTruth
    (fun {_a} {_b} hab => selfSemanticTruth_extensional F hB.codeExt hab)
    (@encodedNontrivial_implies_nontrivial W F hB.encoded)
    (fun F' => hB.hFP F')

end SemanticSelfDescription
