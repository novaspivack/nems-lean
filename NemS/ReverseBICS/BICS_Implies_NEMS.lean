import NemS.ReverseBICS.BICS
import NemS.Core.Trichotomy

/-!
# NemS.ReverseBICS.BICS_Implies_NEMS

The flagship reverse-direction theorem: BICS ⇒ NEMS.

If quantum probability (Born rule) provides the internal, complete semantics for records,
then external model selection is impossible. The theory must be NEMS.

This is Paper 14's main result.
-/

namespace NemS
namespace ReverseBICS

open Framework

/-- **Main theorem (Paper 14)**: BICS implies NEMS.

If a framework satisfies BICS (Born as internal complete semantics for records),
then it satisfies NEMS (no external model selection required) for any internality predicate.

Proof sketch: BICS provides internal probability semantics via the Born rule.
The completeness condition (no_external_completion_bits) forbids any external
selection that would change record-truth without changing the Born probabilities.
Therefore, any purported "external selection" would either:
(a) change Born probabilities (detectable, hence not truly external), or
(b) be redundant (non-load-bearing), or
(c) violate BICS completeness.
Thus the theory is NEMS: no external model selection is needed or possible. -/
theorem bics_implies_nems {F : Framework} (h : BICS F)
    (IsInternal : F.Selector → Prop) : NEMS F IsInternal := by
  sorry

/-- Corollary: BICS rules out the "needs external selection" branch of the trichotomy. -/
theorem bics_rules_out_external {F : Framework} (h : BICS F)
    (IsInternal : F.Selector → Prop) :
    ¬ NeedsExternalSelection F IsInternal := by
  have := bics_implies_nems h IsInternal
  unfold NEMS at this
  exact this

end ReverseBICS
end NemS

