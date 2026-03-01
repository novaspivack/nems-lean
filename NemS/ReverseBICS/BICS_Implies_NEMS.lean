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
  unfold NEMS NeedsExternalSelection
  push_neg
  intro hNC
  -- Assume non-categorical. We need: ∃ S : F.Selector, IsInternal S.
  -- BICS provides internal state ρ and record-to-effect map.
  -- The Born probabilities are model-independent (same ρ for all M).
  -- By BICS completeness: if M1, M2 agree on all probabilities, they're ObsEq.
  -- Since probabilities are model-independent, all models are ObsEq.
  -- This contradicts non-categoricity.
  -- Therefore: the assumption "non-categorical" is false, OR an internal selector exists.
  -- Actually, the logic is: NEMS says ¬(non-cat ∧ ¬∃ internal selector).
  -- We need to show: ¬(non-cat ∧ ¬∃ internal selector).
  -- Equivalently: non-cat → ∃ internal selector.
  -- From BICS: probabilities are model-independent (prob_is_born uses same ρ for all M).
  -- So for any M1, M2: probTruth M1 r = Re(Tr(ρ·recEff(r))) = probTruth M2 r.
  -- By no_external_completion_bits: M1 ObsEq M2.
  -- So all models are ObsEq, hence categorical.
  -- This contradicts hNC.
  exfalso
  have hall_eq : ∀ M1 M2 : F.Model, F.ObsEq M1 M2 := by
    intro M1 M2
    apply h.no_external_completion_bits
    intro r
    rw [h.prob_is_born, h.prob_is_born]
  have hcat : F.ObsCategorical := by
    intro M N
    exact hall_eq M N
  exact hNC hcat

/-- Corollary: BICS rules out the "needs external selection" branch of the trichotomy. -/
theorem bics_rules_out_external {F : Framework} (h : BICS F)
    (IsInternal : F.Selector → Prop) :
    ¬ NeedsExternalSelection F IsInternal := by
  have := bics_implies_nems h IsInternal
  unfold NEMS at this
  exact this

end ReverseBICS
end NemS

