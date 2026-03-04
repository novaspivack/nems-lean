import ChronologyUnderClosure.Core.RecordDynamics
import Closure.Core.ObsSemantics
import Closure.Core.Selector

/-!
# ChronologyUnderClosure.Theorems.RecordNonOverwrite

**Paper 36: Record non-overwrite theorem.**

Overwriting (changing record truth along the feedback) forces non-categoricity:
we cannot have a single world-type (single history) and an overwrite.
So overwrite implies branching (multiple world-types) or, in combination with
other axioms, forces a selector.
-/

set_option autoImplicit false

namespace ChronologyUnderClosure

universe u v

variable {World : Type u} {Obs : Type v} (S : Closure.ObsSemantics World Obs) (F : ChronologyUnderClosure.Feedback World)

/-- **Record non-overwrite theorem**: If at some world `w` and observation `o` we have
an overwrite (o holds at w but not at F w), then the semantics is not categorical
(i.e. there are at least two distinct world-types — "branching"). -/
theorem record_non_overwrite (w : World) (o : Obs) (hOver : ChronologyUnderClosure.Overwrite S F w o) :
    ¬ Closure.ObsSemantics.Categorical S := by
  intro hCat
  have hEq : S.toWorldType w = S.toWorldType (F w) := @Subsingleton.elim S.WorldType hCat (S.toWorldType w) (S.toWorldType (F w))
  have heq : S.ObsEquiv w (F w) := (S.toWorldType_eq_iff w (F w)).mp hEq
  have hHold : S.Holds w o ↔ S.Holds (F w) o := heq o
  cases hOver with
  | intro hw hFw =>
    exact hFw (hHold.mp hw)

end ChronologyUnderClosure
