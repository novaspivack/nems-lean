import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import Hypercomputation.Core.OracleAsSelector
import Hypercomputation.Core.HypercomputerClaim

/-!
# Hypercomputation.Core.Taxonomy

**Five-regime taxonomy of escape routes (Paper 35).**

Defines the failure modes: a purported internal total hypercomputer claim
must fail at least one of: diagonal premise, extensionality, nontriviality,
totality/internality, or closure audit. These are the named logical conditions
for the taxonomy theorem.
-/

set_option autoImplicit false

namespace Hypercomputation

open SelectorStrength

universe u v

variable {α : Type u}
variable (Equiv : α → α → Prop)
variable (Sbool : Strength α Bool)
variable (Sα : Strength α α)

/-- **Fails diagonal premise:** either anti-decider closure fails, or the
fixed-point principle fails for the transformer class. -/
def FailsDiagonalPremise : Prop :=
  ¬ AntiDeciderClosed Sbool Sα ∨ ¬ (∀ F : α → α, Sα F → ∃ d : α, Equiv d (F d))

/-- **Fails extensionality:** the target predicate does not respect Equiv. -/
def FailsExtensionality (T : α → Prop) : Prop :=
  ¬ Extensional Equiv T

/-- **Fails nontriviality:** the target has no true instance or no false instance. -/
def FailsNontriviality (T : α → Prop) : Prop :=
  ¬ Nontrivial T

/-- **Fails internal totality:** no total decider exists at the given strength.
(This is the conclusion of the barrier—we use it in the taxonomy disjunction.) -/
def FailsInternalTotality (T : α → Prop) : Prop :=
  ¬ DecidableAt Sbool T

section ClosureAudit

variable {World : Type u} {Obs : Type v} (sem : Closure.ObsSemantics World Obs)

/-- **Fails closure audit:** the target is selector-sensitive (not invariant
under the observational quotient). Requires worlds as the domain. -/
def FailsClosureAudit (T : World → Prop) : Prop :=
  SelectorSensitive sem T

end ClosureAudit

end Hypercomputation
