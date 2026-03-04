import NemS.Prelude
import SelectorStrength.Core.Deciders
import SelfImprovement.Theorems.Barrier

/-!
# SelfImprovement.Theorems.Stratified

**Stratified improvement principle (Paper 32, T2).**

When hFP is not available (below diagonal closure), the barrier does not apply;
total verifiers may exist for restricted upgrade claim families (witnessed in
Examples.ToyUpgrades). This file states the contrapositive: total certification
and hFP together would contradict the barrier.
-/

set_option autoImplicit false

namespace SelfImprovement

/-- **Stratified improvement (contrapositive of barrier).**

If a total internal verifier exists at strength S and the fixed-point premise hFP
holds, then we get a contradiction (from the barrier). So when hFP is absent,
the barrier does not apply and total verifiers may exist for restricted families. -/
theorem stratified_improvement_schema
    (Cert : Type)
    (Equiv : Cert → Cert → Prop)
    (Claim : Cert → Prop)
    (Sbool : SelectorStrength.Strength Cert Bool)
    (Sα : SelectorStrength.Strength Cert Cert)
    (hExt : SelectorStrength.Extensional Equiv Claim)
    (hNon : SelectorStrength.Nontrivial Claim)
    (hAnti : SelectorStrength.AntiDeciderClosed Sbool Sα)
    (hDec : SelectorStrength.DecidableAt Sbool Claim)
    (hFP : ∀ F : Cert → Cert, Sα F → ∃ d : Cert, Equiv d (F d)) :
    False :=
  no_total_upgrade_certifier Cert Equiv Claim Sbool Sα hExt hNon hAnti hFP hDec

end SelfImprovement
