import Closure.Theorems.AuditSoundness
import Hypercomputation.Core.OracleAsSelector

/-!
# Hypercomputation.Theorems.OracleAudit

**Oracle audit theorems (Paper 35).**

Connects the "oracle" language to the Closure audit machinery.
Any predicate decidable on world-types must be invariant; any non-invariant
predicate cannot be decided at the world-type level—it requires external
selector structure.
-/

set_option autoImplicit false

namespace Hypercomputation

universe u v

variable {World : Type u} {Obs : Type v}

/-- **Oracle claim requires invariance.** Wrapper over Closure's audit soundness.

If a predicate is decidable on world-types (an "oracle" that factors through
the quotient), then it is observationally invariant. -/
theorem oracle_claim_requires_invariance'
    (S : Closure.ObsSemantics World Obs) (T : World → Prop)
    (hDec : Closure.DecidableOnWorldType S T) :
    AuditPassesFor S T :=
  oracle_claim_requires_invariance S T hDec

/-- **Non-invariant target not decidable on world-type.**

If a predicate is selector-sensitive (not invariant), then it cannot be
decided purely on world-types. Any decision procedure would require a
choice of representative—external selection. -/
theorem noninvariant_target_not_decidable_on_world_type
    (S : Closure.ObsSemantics World Obs) (T : World → Prop)
    (h : ¬ S.Invariant T) :
    ¬ Closure.DecidableOnWorldType S T :=
  Closure.not_invariant_implies_not_decidable_on_world_type S T h

/-- **Selector-sensitive targets need external selection.**

Same as above, phrased in Paper 35 vocabulary: selector-sensitive means
the predicate cannot be decided at the world-type level. -/
theorem selector_sensitive_targets_need_external_selection
    (S : Closure.ObsSemantics World Obs) (T : World → Prop)
    (h : SelectorSensitive S T) :
    ¬ Closure.DecidableOnWorldType S T :=
  selector_sensitive_not_decidable_on_world_type S T h

end Hypercomputation
