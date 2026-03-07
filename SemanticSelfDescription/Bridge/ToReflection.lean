import Reflection.Core.SRI_R
import Reflection.Theorems.DiagonalClosure
import SemanticSelfDescription.Core.Claims
import SemanticSelfDescription.Theorems.NoFinalSelfTheory

/-!
# SemanticSelfDescription.Bridge.ToReflection

**Bridge: DiagClosed R supplies the fixed-point premise for BarrierHypotheses.**

When the frame's Code carries SRI_R with DiagClosed R (e.g. from SelfReference
when Obj = Code), and CodeExtensional's CodeEquiv matches SRI Equiv, the
fixed-point premise hFP required by BarrierHypotheses is supplied by Reflection's
restricted_master_fixed_point.

This completes the chain: Reflection (DiagClosed) → BarrierHypotheses → no_final_self_theory.
-/

set_option autoImplicit false

namespace SemanticSelfDescription

universe u v

variable {W : Type u} (F : SelfSemanticFrame W)

/--
**Reflection supplies BarrierHypotheses.hFP.**

When:
- The frame's Code has SRI_R with diagonally closed R (all F' representable)
- CodeExtensional's CodeEquiv coincides with SRI_R.Equiv
- quote is identity (unityped setting: F(quote p) = F p)

then for every F' : F.Code → F.Code, Reflection gives a fixed point d with
CodeEquiv d (F' d), yielding the hFP premise for BarrierHypotheses.
-/
theorem reflection_supplies_hFP
    (codeExt : CodeExtensional F)
    (R : (F.Code → F.Code) → Prop)
    [sri : Reflection.SRI_R F.Code F.Code R]
    (hDiag : Reflection.DiagClosed R)
    (hEquiv : ∀ a b, codeExt.CodeEquiv a b ↔ sri.Equiv a b)
    (hR : ∀ F' : F.Code → F.Code, R F')
    (hQuoteId : ∀ p : F.Code, sri.quote p = p) :
    ∀ F' : F.Code → F.Code, ∃ d : F.Code, codeExt.CodeEquiv d (F' d) := by
  intro F'
  obtain ⟨p, hp⟩ := Reflection.restricted_master_fixed_point hDiag F' (hR F')
  use p
  have hp' : sri.Equiv p (F' p) := by rw [hQuoteId p] at hp; exact hp
  exact (hEquiv p (F' p)).mpr hp'

/--
**BarrierHypotheses from Reflection.**

When the frame has code extensionality, encoded nontriviality, and the
Reflection setup above (SRI_R on Code with DiagClosed, CodeEquiv = Equiv,
quote = id), we obtain full BarrierHypotheses and thus no_final_self_theory.
-/
def barrier_hypotheses_from_reflection
    (codeExt : CodeExtensional F)
    [EncodedNontrivial F]
    (R : (F.Code → F.Code) → Prop)
    [sri : Reflection.SRI_R F.Code F.Code R]
    (hDiag : Reflection.DiagClosed R)
    (hEquiv : ∀ a b, codeExt.CodeEquiv a b ↔ sri.Equiv a b)
    (hR : ∀ F' : F.Code → F.Code, R F')
    (hQuoteId : ∀ p : F.Code, sri.quote p = p) :
    BarrierHypotheses F :=
  ⟨codeExt, inferInstance, reflection_supplies_hFP F codeExt R hDiag hEquiv hR hQuoteId⟩

end SemanticSelfDescription
