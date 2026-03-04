import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import Learning.Core.Certificates

/-!
# Learning.Core.SelfTrust

**Self-certifier at strength (Paper 30).**

A **self-certifier at strength S** is a total internal verifier for the claim
predicate at that strength: i.e. `DecidableAt S Claim` in SelectorStrength
terminology. We define terminology and lemmas.
-/

set_option autoImplicit false

namespace Learning

universe u

variable {Cert : Type u}

/-- **Self-certifier at strength S**: there exists a total internal verifier
for `Claim` in strength class `S`. This is exactly `DecidableAt S Claim`. -/
def SelfCertifierAtStrength (S : SelectorStrength.Strength Cert Bool) (Claim : Cert → Prop) : Prop :=
  SelectorStrength.DecidableAt S Claim

theorem selfCertifierAtStrength_iff (S : SelectorStrength.Strength Cert Bool) (Claim : Cert → Prop) :
    SelfCertifierAtStrength S Claim ↔ SelectorStrength.DecidableAt S Claim :=
  Iff.rfl

end Learning
