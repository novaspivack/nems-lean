import NemS.Prelude
import Learning.Theorems.SelfTrustBarrier
import SelfAwareness.Core.SelfModel

/-!
# SelfAwareness.Theorems.SelectorNecessity

**Selector necessity from self-model multiplicity (Paper 33).**

When two fixed points are observationally indistinguishable, "which is actual"
is not decidable from world-types (Closure no-free-bits). Selection among
indistinguishable fixed points cannot be total-effective under diagonal capability
(Paper 29 barrier). Schema statements; full formalization ties to Closure's
observational semantics and audit soundness.
-/

set_option autoImplicit false

namespace SelfAwareness

/-- **Selector necessary from multiplicity (schema).**

When an update has multiple fixed points, identifying "the actual one" is not
determined by the update rule alone; it requires selection. Under diagonal
capability, such selection cannot be total-effective internally (Paper 29 barrier). -/
theorem selection_not_total_effective
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

/-- Alias for selector_necessary_from_multiplicity: same barrier (selection as decider). -/
theorem selector_necessary_from_multiplicity
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
  selection_not_total_effective Cert Equiv Claim Sbool Sα hExt hNon hAnti hFP

end SelfAwareness
