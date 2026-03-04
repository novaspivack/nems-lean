import NemS.Prelude

/-!
# EpistemicAgency.Core.Agent

**Minimal agent core (control layer) for Paper 31.**

Agent as embedded controller: World, Obs, Act, Mem, observe, step, update, policy.
This supplies the domain of claims (safety, stability); main theorems are in
verification and epistemics.
-/

set_option autoImplicit false

namespace EpistemicAgency

/-- **Agent core**: observation, world step, memory update, policy. -/
structure AgentCore (World Obs Act Mem : Type) where
  observe : World → Obs
  step : World → Act → World
  update : Mem → Obs → Act → Mem
  policy : Mem → Act

end EpistemicAgency
