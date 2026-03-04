import NemS.Prelude
import Learning.Theorems.SelfTrustBarrier
import SelfAwareness.Core.ClaimFamilies

/-!
# SelfAwareness.Theorems.Hierarchy

**Self-awareness hierarchy with strict separations (Paper 33).**

C0 has a total certifier (witnessed in Examples.ToyHierarchy); C2 (nontrivial extensional
claim class under diagonal capability) has no total certifier (Paper 30 barrier).
-/

set_option autoImplicit false

namespace SelfAwareness

/-- **No total certifier for C2 under diagonal capability.**

When the claim predicate is extensional and nontrivial and the strength has
anti-decider closure and hFP, no total internal verifier exists. This is the
Paper 30 barrier; C2 is any such claim class. -/
theorem no_total_certifier_C2
    (Cert : Type)
    (Equiv : Cert → Cert → Prop)
    (Claim : Cert → Prop)
    (Sbool : SelectorStrength.Strength Cert Bool)
    (Sα : SelectorStrength.Strength Cert Cert)
    (hExt : SelectorStrength.Extensional Equiv Claim)
    (hNon : SelectorStrength.Nontrivial Claim)
    (hAnti : SelectorStrength.AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : Cert → Cert, Sα F → ∃ d : Cert, Equiv d (F d)) :
    ¬ SelectorStrength.DecidableAt Sbool Claim :=
  Learning.no_total_self_certifier Equiv Claim Sbool Sα hExt hNon hAnti hFP

end SelfAwareness
