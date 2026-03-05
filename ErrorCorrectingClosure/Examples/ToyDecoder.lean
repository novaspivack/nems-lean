import ErrorCorrectingClosure.Core.DecodingModel
import ErrorCorrectingClosure.Theorems.DecoderBarrier
import SelectorStrength.Core.Strength

set_option autoImplicit false

/-!
# ErrorCorrectingClosure.Examples.ToyDecoder

**Paper 43: Toy decoding scenario.**

Two instance types (consistent / inconsistent) and codes that claim consistency.
The decoder-claim predicate is nontrivial; the barrier applies under hFP and
anti-decider closure.
-/

namespace ErrorCorrectingClosure

/-- Code that claims the consistent instance is consistent (holds). -/
def codeConsistentClaim : DecodeCode := ⟨InstanceIndex.consistent, true⟩

/-- Code that claims the consistent instance is inconsistent (does not hold). -/
def codeInconsistentClaim : DecodeCode := ⟨InstanceIndex.consistent, false⟩

theorem codeConsistentClaim_holds : decoderClaim codeConsistentClaim := by
  simp [decoderClaim, codeConsistentClaim, isConsistent]

theorem codeInconsistentClaim_fails : ¬ decoderClaim codeInconsistentClaim := by
  simp [decoderClaim, codeInconsistentClaim, isConsistent]

/-- Toy witness: decoder-claim predicate is nontrivial (already in DecoderBarrier;
these codes are explicit witnesses). -/
theorem toy_decoder_claim_nontrivial : SelectorStrength.Nontrivial decoderClaim :=
  decoderClaim_nontrivial

/-- Barrier applies to decoder-claim: no total decider under hFP and anti-closure. -/
theorem toy_no_total_decider_decoder
    (Sbool : SelectorStrength.Strength DecodeCode Bool)
    (Sα : SelectorStrength.Strength DecodeCode DecodeCode)
    (hAnti : SelectorStrength.AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : DecodeCode → DecodeCode, Sα F → ∃ d : DecodeCode, d = F d) :
    ¬ SelectorStrength.DecidableAt Sbool decoderClaim :=
  no_total_decider_decoder_claim Sbool Sα hAnti hFP

end ErrorCorrectingClosure
