import NemS.Prelude
import Learning.Theorems.SelfTrustBarrier

/-!
# EpistemicAgency.Theorems.NoSelfCertifierImported

**Imported no-go from Paper 30 (Learning): no total internal self-certifier.**

This module re-exports the Learning library's barrier so that Paper 31 can cite it
as the "individual no-go" before proving society can do strictly more.
-/

set_option autoImplicit false

namespace EpistemicAgency

/-- **No self-certifier (imported from Paper 30).**

For any nontrivial extensional claim predicate, if the strength level is
anti-decider closed and has the fixed-point premise (hFP), then there is no
total internal verifier for the claim at that strength. This is
`Learning.no_total_self_certifier`. -/
theorem no_self_certifier
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

end EpistemicAgency
