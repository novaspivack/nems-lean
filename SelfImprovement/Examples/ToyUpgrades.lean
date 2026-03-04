import NemS.Prelude
import EpistemicAgency.Core.ClaimDomain
import EpistemicAgency.Core.Protocol
import EpistemicAgency.Theorems.ProtocolStrictImprovement
import EpistemicAgency.Theorems.Diversity
import EpistemicAgency.Examples.ToySociety

/-!
# SelfImprovement.Examples.ToyUpgrades

**Toy upgrade-claim domain (Paper 32).**

Finite set of "upgrade scenarios" as claim IDs; two auditors with complementary
coverage. Reuses EpistemicAgency.Examples.ToySociety: the same ClaimDomain and
society serve as upgrade-verification toy (claim ID = upgrade scenario ID).
-/

set_option autoImplicit false

namespace SelfImprovement

open EpistemicAgency EpistemicAgency.ClaimDomain

/-- Upgrade-claim domain: reuse ToySociety's domain (Fin 4, toy truth). -/
def upgradeToyDomain : EpistemicAgency.ClaimDomain := EpistemicAgency.toyDomain

/-- Toy society for upgrade verification: two roles with complementary coverage. -/
def upgradeToySociety : Society upgradeToyDomain := EpistemicAgency.toySociety

/-- Society is sound. -/
theorem upgradeToySocietySound : SocietySound upgradeToySociety := EpistemicAgency.toySocietySound

/-- Strict improvement: society covers all upgrade scenarios; each individual covers two. -/
theorem toy_upgrade_strict_improvement (i : Fin 4) :
    i ∈ societyCover upgradeToySociety ∧ (i ∉ EpistemicAgency.toyC1 ∨ i ∉ EpistemicAgency.toyC2) :=
  EpistemicAgency.toy_strict_improvement i

/-- Diversity necessity: the two coverage sets differ. -/
theorem toy_upgrade_diversity_necessary : ¬ ∃ C, Homogeneous upgradeToySociety C :=
  EpistemicAgency.toy_diversity_necessary

end SelfImprovement
