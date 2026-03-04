import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import SelectorStrength.Theorems.BarrierSchema
import Learning.Core.SelfTrust

/-!
# Learning.Theorems.SelfTrustBarrier

**No total internal self-certifier (Paper 30 headline).**

If the claim predicate is extensional and nontrivial, and the strength level is
anti-decider closed with a fixed-point engine (hFP), then there is no total
internal verifier for the claim at that strength. This is the barrier schema
(Paper 29) instantiated to certificate space: we prove it by composing with
SelectorStrength.Theorems.BarrierSchema.
-/

set_option autoImplicit false

namespace Learning

universe u

variable {Cert : Type u}

/-- **No total internal self-certifier at strength S.**

If `Claim` is extensional and nontrivial, and the strength pair `(Sbool, Sα)` is
anti-decider closed with fixed-point premise `hFP`, then there is no total
internal verifier for `Claim` in `Sbool`. Immediate from Paper 29 barrier
schema with α = Cert, T = Claim. -/
theorem no_total_self_certifier
    (Equiv : Cert → Cert → Prop)
    (Claim : Cert → Prop)
    (Sbool : SelectorStrength.Strength Cert Bool)
    (Sα : SelectorStrength.Strength Cert Cert)
    (hExt : SelectorStrength.Extensional Equiv Claim)
    (hNon : SelectorStrength.Nontrivial Claim)
    (hAnti : SelectorStrength.AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : Cert → Cert, Sα F → ∃ d : Cert, Equiv d (F d)) :
    ¬ SelectorStrength.DecidableAt Sbool Claim :=
  SelectorStrength.no_total_decider_at_strength_nontrivial Equiv Claim hExt hNon Sbool Sα hAnti hFP

/-- Same theorem phrased as "no self-certifier at strength". -/
theorem no_self_certifier_at_strength
    (Equiv : Cert → Cert → Prop)
    (Claim : Cert → Prop)
    (Sbool : SelectorStrength.Strength Cert Bool)
    (Sα : SelectorStrength.Strength Cert Cert)
    (hExt : SelectorStrength.Extensional Equiv Claim)
    (hNon : SelectorStrength.Nontrivial Claim)
    (hAnti : SelectorStrength.AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : Cert → Cert, Sα F → ∃ d : Cert, Equiv d (F d)) :
    ¬ SelfCertifierAtStrength Sbool Claim :=
  no_total_self_certifier Equiv Claim Sbool Sα hExt hNon hAnti hFP

end Learning
