import NemS.Prelude
import Closure.Core.ObsSemantics

/-!
# BlackHoles.Core.RecordFragments

**Paper 37: Record fragments for black hole information.**

Worlds represent black-hole scenarios (e.g. outside thermal, infalling, unitarity);
observational propositions are record fragments. Consistency means the fragments
close without external selection (categorical or internal selector).
-/

set_option autoImplicit false

namespace BlackHoles

universe u v

variable {World : Type u} {Obs : Type v} (S : Closure.ObsSemantics World Obs)

/-- **Information-erasing appearance**: at world `w`, observation `o` holds,
but at world `w'` (e.g. "after" or "from another perspective") it does not,
so the record appears to be erased or inconsistent across fragments. -/
def ErasingAppearance (w w' : World) (o : Obs) : Prop :=
  S.Holds w o ∧ ¬ S.Holds w' o

/-- **Record consistency theorem (abstract)**: If we have an erasing appearance
(two worlds disagree on an observation), then the semantics is not categorical
(i.e. there are at least two world-types; selection is required in the sense of
Paper 27). Under classical Choice, a selector exists; internal/effective
selector is constrained by the diagonal barriers (Paper 29/35). -/
theorem record_consistency_abstract (w w' : World) (o : Obs)
    (hErase : ErasingAppearance S w w' o) :
    ¬ Closure.ObsSemantics.Categorical S := by
  intro hCat
  have hEq : S.toWorldType w = S.toWorldType w' :=
    @Subsingleton.elim S.WorldType hCat (S.toWorldType w) (S.toWorldType w')
  have heq : S.ObsEquiv w w' := (S.toWorldType_eq_iff w w').mp hEq
  cases hErase with
  | intro hw hw' =>
    exact hw' (heq o |>.mp hw)

end BlackHoles
