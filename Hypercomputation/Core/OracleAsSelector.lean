import Closure.Core.ObsSemantics
import Closure.Theorems.AuditSoundness

/-!
# Hypercomputation.Core.OracleAsSelector

**Oracle-as-selector audit vocabulary (Paper 35).**

Thin wrappers over Closure's observational invariance and audit soundness.
A purported "oracle" deciding a predicate is not automatically problematic;
the issue arises when the predicate is **selector-sensitive** (not invariant
under the observational quotient). Then the decision requires extra selector
structure—i.e., external selection.
-/

set_option autoImplicit false

namespace Hypercomputation

universe u v

variable {World : Type u} {Obs : Type v}

/-- A predicate `T` **passes the audit** if it is observationally invariant:
equivalent worlds get the same truth value. Deciding such a predicate
does not require a choice of representative. -/
def AuditPassesFor (S : Closure.ObsSemantics World Obs) (T : World → Prop) : Prop :=
  S.Invariant T

/-- A predicate is **selector-sensitive** if it is not invariant under the
observational quotient. Any decider for such a predicate cannot factor
through world-types—it must depend on a choice of representative (selector). -/
def SelectorSensitive (S : Closure.ObsSemantics World Obs) (T : World → Prop) : Prop :=
  ¬ AuditPassesFor S T

/-- **Audit passes iff invariant.** -/
theorem audit_passes_iff_invariant (S : Closure.ObsSemantics World Obs) (T : World → Prop) :
    AuditPassesFor S T ↔ S.Invariant T :=
  Iff.rfl

/-- **Oracle claim requires invariance (Paper 35).**

If a predicate is decidable on world-types (factors through the quotient),
then it is observationally invariant. So any "oracle" that claims to decide
a predicate at the world-type level must be deciding an invariant predicate.
This is the audit soundness theorem. -/
theorem oracle_claim_requires_invariance
    (S : Closure.ObsSemantics World Obs) (T : World → Prop)
    (hDec : Closure.DecidableOnWorldType S T) :
    AuditPassesFor S T :=
  Closure.audit_soundness S T hDec

/-- **Selector-sensitive targets cannot be decided on world-type.**

If a predicate is not invariant (selector-sensitive), then it cannot be
decided purely on world-types. Any decider would require extra selector
structure—external selection. This is the contrapositive of audit soundness. -/
theorem selector_sensitive_not_decidable_on_world_type
    (S : Closure.ObsSemantics World Obs) (T : World → Prop)
    (h : SelectorSensitive S T) :
    ¬ Closure.DecidableOnWorldType S T :=
  Closure.not_invariant_implies_not_decidable_on_world_type S T
    ((Iff.not (audit_passes_iff_invariant S T)).mp h)

end Hypercomputation
