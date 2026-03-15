import InternalitySchema.Instances.Closure
import NemS.Core.Trichotomy

/-!
# InternalitySchema.Theorems.Foundationality

**Meta-Principle 2 (Fundamentality as Internal Completion).**

A theory counts as foundational not merely by providing laws, but by internally
bearing the burden of the determinacy required to make those laws semantically
complete on the relevant record fragment.
-/

set_option autoImplicit false

namespace InternalitySchema

open NemS NemS.Framework

/--
**Foundational** (Meta-Principle 2): no external selection needed.
A framework is foundational iff it satisfies NEMS: it either has no load-bearing
ambiguity (ObsCategorical) or supplies an internal selector.
-/
def Foundational (F : Framework) (IsInternal : F.Selector → Prop) : Prop :=
  NEMS F IsInternal

/--
**Foundational iff internal completion.**
Foundational ↔ categorical ∨ internal selector.
This is the formal content of Meta-Principle 2: a theory counts as foundational
precisely when it internally bears the burden of determinacy (no outsourcing).
-/
theorem foundational_iff_internal_completion (F : Framework) (IsInternal : F.Selector → Prop) :
    Foundational F IsInternal ↔ F.ObsCategorical ∨ ∃ S : F.Selector, IsInternal S :=
  nems_iff_cat_or_internal

/--
**Foundational implies no external selection.**
-/
theorem foundational_implies_no_external_selection
    (F : Framework) (IsInternal : F.Selector → Prop) (h : Foundational F IsInternal) :
    ¬ NeedsExternalSelection F IsInternal := h

end InternalitySchema
