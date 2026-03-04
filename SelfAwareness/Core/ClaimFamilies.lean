import NemS.Prelude
import SelectorStrength.Core.Deciders

/-!
# SelfAwareness.Core.ClaimFamilies

**Claim languages and self-awareness at strength (Paper 33).**

Claim type, semantics, claim classes (C0, C1, C2). Self-awareness at strength S
= total internal certification over a claim class (DecidableAt restricted to class).
-/

set_option autoImplicit false

namespace SelfAwareness

/-- Claim language: type of claims and semantics. -/
structure ClaimLang where
  Claims : Type
  Sem : Claims → Prop

/-- Self-awareness at strength: total internal certification over the full claim type.
  (Restricted to a class in the paper; here we use the barrier's DecidableAt.) -/
def SelfAwareAt (Cert : Type) (Sbool : SelectorStrength.Strength Cert Bool) (Claim : Cert → Prop) : Prop :=
  SelectorStrength.DecidableAt Sbool Claim

end SelfAwareness
