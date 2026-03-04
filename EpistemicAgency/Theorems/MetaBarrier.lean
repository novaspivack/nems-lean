import NemS.Prelude
import Learning.Theorems.SelfTrustBarrier

/-!
# EpistemicAgency.Theorems.MetaBarrier

**Meta-barrier: society does not abolish diagonal constraints (Paper 31).**

If the society-plus-protocol is treated as a single diagonal-capable system
attempting universal total self-certification for a nontrivial extensional
claim predicate, then Paper 30 applies at the societal level: no such universal
total internal self-certifier exists.
-/

set_option autoImplicit false

namespace EpistemicAgency

/-- **Meta-barrier (schema).**

If a system (e.g. society-plus-protocol viewed as one agent) is diagonal-capable
and attempts to provide a universal total internal self-certifier for a
nontrivial extensional claim predicate, then no such certifier exists.
This is Paper 30 applied at the societal level. -/
theorem meta_barrier_society
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
