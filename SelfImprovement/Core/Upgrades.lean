import NemS.Prelude
import SelectorStrength.Core.Deciders

/-!
# SelfImprovement.Core.Upgrades

**Upgrades as certificates (Paper 32).**

Agent and upgrade types; certificate type Cert = Agent × Upgrade;
goodness predicate Good. Used by Barrier and other modules.
-/

set_option autoImplicit false

namespace SelfImprovement

/-- Agent description type (code, policy, model state). -/
def Agent := Type

/-- Upgrade description type. -/
def Upgrade := Type

/-- Certificate for upgrade verification: (agent, proposed upgrade). -/
def UpCert (Agent Upgrade : Type) := Agent × Upgrade

/-- Goodness predicate: upgrade u is good/safe for agent a. -/
def Good (Agent Upgrade : Type) := UpCert Agent Upgrade → Prop

end SelfImprovement
