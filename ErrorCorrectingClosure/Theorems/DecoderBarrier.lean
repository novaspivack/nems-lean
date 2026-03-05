import ErrorCorrectingClosure.Core.DecodingModel
import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import SelectorStrength.Theorems.BarrierSchema

set_option autoImplicit false

/-!
# ErrorCorrectingClosure.Theorems.DecoderBarrier

**Paper 43: No total-effective decoder under diagonal capability.**

The uniform decoder-claim predicate (does the encoded instance's consistency match
the claimed value?) is extensional and nontrivial. Under AntiDeciderClosed and hFP,
no total-effective decider exists for it over encoded instances.
-/

namespace ErrorCorrectingClosure

/-- The decoder-claim predicate is extensional for equality on codes. -/
theorem decoderClaim_extensional :
    SelectorStrength.Extensional (· = ·) decoderClaim := by
  intro x y heq
  rw [heq]

/-- The decoder-claim predicate is nontrivial: (consistent, true) holds,
(consistent, false) does not. -/
theorem decoderClaim_nontrivial : SelectorStrength.Nontrivial decoderClaim := by
  refine ⟨⟨⟨InstanceIndex.consistent, true⟩, by simp [decoderClaim, isConsistent]⟩,
    ⟨⟨InstanceIndex.consistent, false⟩, by simp [decoderClaim, isConsistent]⟩⟩

/-- **Decoder barrier:** Under AntiDeciderClosed and hFP at strength S,
no total decider in Sbool exists for the uniform decoder-claim predicate on codes. -/
theorem no_total_decider_decoder_claim
    (Sbool : SelectorStrength.Strength DecodeCode Bool)
    (Sα : SelectorStrength.Strength DecodeCode DecodeCode)
    (hAnti : SelectorStrength.AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : DecodeCode → DecodeCode, Sα F → ∃ d : DecodeCode, d = F d) :
    ¬ SelectorStrength.DecidableAt Sbool decoderClaim :=
  SelectorStrength.no_total_decider_at_strength_nontrivial (· = ·) decoderClaim
    decoderClaim_extensional decoderClaim_nontrivial Sbool Sα hAnti hFP

end ErrorCorrectingClosure
