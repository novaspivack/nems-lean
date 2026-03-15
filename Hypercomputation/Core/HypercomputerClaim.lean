import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders

/-!
# Hypercomputation.Core.HypercomputerClaim

**Hypercomputer claim interface (Paper 35).**

Minimal packaging of the "internal total hypercomputer" claim.
A purported hypercomputer for predicate T at strength S is a total decider
for T in the class S. The real content comes from the barrier theorems;
this module centralizes the language for Paper-35-facing theorem names.
-/

set_option autoImplicit false

namespace Hypercomputation

open SelectorStrength

universe u

variable {α : Type u}

/-- A **hypercomputer claim** bundles a target predicate with extensionality
and nontriviality. This is the Paper 35 claim shape. -/
structure HypercomputerClaim (Equiv : α → α → Prop) where
  target      : α → Prop
  extensional : Extensional Equiv target
  nontrivial  : Nontrivial target

/-- A purported **total effective hypercomputer** at strength S for target T:
T has some total decider in class S. -/
def HasHypercomputerAt (S : Strength α Bool) (T : α → Prop) : Prop :=
  DecidableAt S T

/-- **Internal hypercomputer claim:** the target is decided at the nominated
internal strength. Same as `HasHypercomputerAt`; the "internal" qualifier
is semantic (the strength is the one we deem internal, e.g. computable).
This is the main interface for the no-internal-hypercomputer theorem. -/
def HasInternalHypercomputerAt (S : Strength α Bool) (T : α → Prop) : Prop :=
  DecidableAt S T

/-- A **hypercomputer scenario** bundles strength, target, equivalence,
and the barrier premises. Useful for stating taxonomy theorems. -/
structure HypercomputerScenario (α : Type u) where
  Equiv   : α → α → Prop
  Sbool   : Strength α Bool
  Sα      : Strength α α
  target  : α → Prop
  ext     : Extensional Equiv target
  nontriv : Nontrivial target

end Hypercomputation
