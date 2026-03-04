import NemS.Prelude
import Learning.Theorems.SelfTrustBarrier

/-!
# SelfImprovement.Theorems.Barrier

**Self-Improvement Barrier Theorem (Paper 32, T1).**

No total internal self-upgrade certifier under diagonal capability.
Wrapper around Paper 30 (Learning.no_total_self_certifier) with Cert = Agent × Upgrade.
-/

set_option autoImplicit false

namespace SelfImprovement

/-- **No total upgrade certifier.**

For any extensional, nontrivial upgrade-claim predicate (Good : Cert → Prop),
if the strength is anti-decider closed and has the fixed-point premise (hFP),
then there is no total internal verifier for that claim at that strength.
This is Paper 30 applied to upgrade certificates (e.g. Cert = Agent × Upgrade). -/
theorem no_total_upgrade_certifier
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

end SelfImprovement
