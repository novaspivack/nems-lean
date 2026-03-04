import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import Learning.Theorems.SelfTrustBarrier

/-!
# Learning.Examples.ToyGuarantee

**Toy guarantee predicate (Paper 30).**

A minimal concrete claim on certificates (Nat): "certificate is zero". This is
nontrivial (0 holds, 1 does not) and extensional for equality. The barrier
theorem applies: for any strength that is anti-decider closed and has hFP,
no total internal verifier exists for this claim. We do not instantiate a
concrete strength here; we only show the claim satisfies the barrier's hypotheses.
-/

set_option autoImplicit false

namespace Learning

namespace Examples

/-- **Toy claim**: certificate 0 is "valid", any other is not. -/
def ToyClaim (n : Nat) : Prop := n = 0

/-- ToyClaim is extensional for equality. -/
theorem toyClaim_extensional : SelectorStrength.Extensional (α := Nat) (· = ·) ToyClaim := by
  intro _ _ h
  simp only [ToyClaim]
  rw [h]

/-- ToyClaim is nontrivial: 0 satisfies, 1 does not. -/
theorem toyClaim_nontrivial : SelectorStrength.Nontrivial ToyClaim := by
  refine ⟨⟨0, rfl⟩, ⟨1, Nat.one_ne_zero⟩⟩

/-- **Barrier for toy claim**: for any strength (Sbool, Sα) that is anti-decider
closed and has the fixed-point premise, no total internal verifier exists for
ToyClaim. -/
theorem no_total_self_certifier_toy
    (Sbool : SelectorStrength.Strength Nat Bool)
    (Sα : SelectorStrength.Strength Nat Nat)
    (hAnti : SelectorStrength.AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : Nat → Nat, Sα F → ∃ d : Nat, d = F d) :
    ¬ SelectorStrength.DecidableAt Sbool ToyClaim :=
  no_total_self_certifier (· = ·) ToyClaim Sbool Sα toyClaim_extensional toyClaim_nontrivial
    hAnti (fun F hF => by obtain ⟨d, hd⟩ := hFP F hF; exact ⟨d, hd⟩)

end Examples

end Learning
