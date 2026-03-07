import SemanticSelfDescription.Core.Claims
import SemanticSelfDescription.Core.SelfTheory
import SemanticSelfDescription.Bridge.ToSelectorStrength
import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import SelectorStrength.Theorems.BarrierSchema
import SelectorStrength.Instances.Trivial

/-!
# SemanticSelfDescription.Theorems.NoFinalSelfTheory

**Necessary Incompleteness of Internal Semantic Self-Description.**

No sufficiently expressive realized universe can internally contain a final,
faithful, complete theory of its own realized semantics.

This is stronger than "no total effective decider" — it is a theorem about
internal semantic self-capture at the world level. The proof reduces to the
SelectorStrength barrier schema.
-/

set_option autoImplicit false

namespace SemanticSelfDescription

universe u v

variable {W : Type u} (F : SelfSemanticFrame W)

/--
**Barrier hypotheses** for the no-final-self-theory theorem.

A frame satisfies these when:
- It has code extensionality (CodeEquiv with decode_ext)
- It is encoded nontrivial (both true and false codes exist)
- The fixed-point premise holds: every transformer F : Code → Code has a
  fixed point d with CodeEquiv d (F d)

The fixed-point premise is supplied by Reflection when the frame's Code
carries an SRI_R with DiagClosed R (e.g. from SelfReference when Obj = Code).
-/
structure BarrierHypotheses (F : SelfSemanticFrame W) where
  codeExt    : CodeExtensional F
  encoded    : EncodedNontrivial F
  hFP        : ∀ F' : F.Code → F.Code, ∃ d : F.Code, codeExt.CodeEquiv d (F' d)

/--
**Flagship theorem: No final internal self-theory.**

Let F be a self-semantic frame with:
- code extensionality (self-semantic truth respects CodeEquiv)
- encoded nontriviality (both true and false encoded claims exist)
- the fixed-point premise (diagonal capability)

Then there is no internal theory T that is simultaneously total, faithful,
and exact on the entire encoded self-semantic claim family.

In slogan form: **No universe can internally contain a final complete faithful
theory of its own realized semantics.**
-/
theorem no_final_self_theory
    [EncodedNontrivial F]
    (ext : CodeExtensional F)
    (hFP : ∀ F' : F.Code → F.Code, ∃ d : F.Code, ext.CodeEquiv d (F' d)) :
    ¬ ∃ T : InternalSelfTheory F, FinalSelfTheory T := by
  intro ⟨T, hT⟩
  have hDec : SelectorStrength.DecidableAt SelectorStrength.S_all F.selfSemanticTruth :=
    finalTheory_implies_decidableAt F T hT
  have hExt : SelectorStrength.Extensional ext.CodeEquiv F.selfSemanticTruth :=
    fun {a} {b} hab => selfSemanticTruth_extensional F ext hab
  have hNon : SelectorStrength.Nontrivial F.selfSemanticTruth :=
    encodedNontrivial_implies_nontrivial F
  exact SelectorStrength.no_total_decider_all ext.CodeEquiv F.selfSemanticTruth
    hExt hNon (fun F' => hFP F') hDec

/--
**Corollary** using the packaged BarrierHypotheses.
-/
theorem no_final_self_theory' (hBarrier : BarrierHypotheses F) :
    ¬ ∃ T : InternalSelfTheory F, FinalSelfTheory T :=
  by have : EncodedNontrivial F := hBarrier.encoded; exact no_final_self_theory F hBarrier.codeExt hBarrier.hFP

end SemanticSelfDescription
