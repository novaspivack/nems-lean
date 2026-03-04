import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders

/-!
# Learning.Core.Certificates

**Certificate semantics (Paper 30).**

Certificates live in a type `Cert`. A **claim** is a predicate `Claim : Cert → Prop`
(what a certificate asserts; e.g. "this guarantee holds"). We reuse SelectorStrength's
decider and extensionality notions: total decider, extensional for an equivalence,
nontrivial. No new definitions beyond terminology and re-export.
-/

set_option autoImplicit false

namespace Learning

universe u

variable {Cert : Type u}

/-- **Claim** (guarantee predicate): in the Learning library we use `Claim` as the
name for the predicate that certificates assert. It is any `Cert → Prop`. -/
def Claim := Cert → Prop

/-- Re-export SelectorStrength's Extensional for use with Cert and Claim. -/
scoped notation "ExtensionalCert" => SelectorStrength.Extensional

/-- Re-export TotalDecider: δ is a total decider for Claim. -/
scoped notation "TotalDeciderClaim" => SelectorStrength.TotalDecider

/-- Re-export Nontrivial for Claim. -/
scoped notation "NontrivialClaim" => SelectorStrength.Nontrivial

/-- Re-export DecidableAt: Claim has a decider in strength class S. -/
scoped notation "DecidableAtCert" => SelectorStrength.DecidableAt

end Learning
