import Closure.Core.ObsSemantics
import Closure.Core.Selector
import Closure.Core.Internal

/-!
# Closure.Core.Canonicalization

**Canonicalization** is a function `canon : World → World` that picks a
representative in each observational equivalence class: `canon w ~ w` and
`canon w₁ = canon w₂ ↔ w₁ ~ w₂`. It is the clean "gauge-fixing" that induces
a selector. The audit target is: **if** a theory can decide non-invariant
properties, it must have internal access to such a canon (or equivalent
symmetry-breaking).

* A canonicalization induces a selector (no Choice beyond picking one rep per type).
* If `canon` is internal, the induced selector is internal—this is the
  **nailed** path to `DeciderImpliesInternalSelector` under a concrete
  internality model (computable, definable).
-/

set_option autoImplicit false

namespace Closure

universe u v

variable {World : Type u} {Obs : Type v} (S : ObsSemantics World Obs)

/-- **Canonicalization** for observational semantics `S`: a function that
maps each world to a representative of its world-type, with same-type
worlds mapping to the same canonical world. -/
structure Canonicalization where
  /-- The canonical representative of the class of `w`. -/
  canon : World → World
  /-- `canon w` is observationally equivalent to `w`. -/
  canon_equiv : ∀ w, S.ObsEquiv (canon w) w
  /-- Same world-type iff same canonical representative. -/
  canon_same_type_iff : ∀ w₁ w₂, (canon w₁ = canon w₂) ↔ S.ObsEquiv w₁ w₂

variable (C : Canonicalization S)

namespace Canonicalization

/-- The canonical representative of a world lies in the correct class. -/
theorem toWorldType_canon (w : World) : S.toWorldType (C.canon w) = S.toWorldType w :=
  (S.toWorldType_eq_iff (C.canon w) w).mpr (C.canon_equiv w)

/-- For each world-type `t`, there is a world (e.g. `canon w` for any `w` with
`toWorldType w = t`) whose type is `t`. So we can define a section. -/
theorem exists_rep (t : S.WorldType) : ∃ w : World, S.toWorldType w = t :=
  Quotient.exists_rep (s := S.obsEquivSetoid) t

/-- The map `t ↦ canon (choose (exists_rep t))` is a section: applying
`toWorldType` gives back `t`. -/
theorem section_of_canon (t : S.WorldType) (w : World) (hw : S.toWorldType w = t) :
    S.toWorldType (C.canon w) = t := by
  rw [← hw]; exact (S.toWorldType_eq_iff (C.canon w) w).mpr (C.canon_equiv w)

end Canonicalization

/-- For each world-type there is a representative (used when building selector from canon). -/
theorem canon_exists_rep (S : ObsSemantics World Obs) (C : Canonicalization S) (t : S.WorldType) :
    ∃ w : World, S.toWorldType w = t := by
  have _ := C
  exact Quotient.exists_rep (s := S.obsEquivSetoid) t

/-- Canon sends a world to same-type class; used for selector section proof. -/
theorem canon_section_of_canon (S : ObsSemantics World Obs) (C : Canonicalization S) (t : S.WorldType) (w : World)
    (hw : S.toWorldType w = t) : S.toWorldType (C.canon w) = t := by
  have _ := C
  rw [← hw]; exact (S.toWorldType_eq_iff (C.canon w) w).mpr (C.canon_equiv w)

/-- **Canonicalization induces a selector.**  Given a canonicalization,
we get a section of the quotient by defining `sel t = canon w` for any
world `w` in class `t` (e.g. `Classical.choose (exists_rep t)`). -/
theorem selector_of_canonicalization (C : Canonicalization S) : Nonempty (Selector S) := by
  let w (t : S.WorldType) : World := Classical.choose (canon_exists_rep S C t)
  have hw (t : S.WorldType) : S.toWorldType (w t) = t :=
    Classical.choose_spec (canon_exists_rep S C t)
  let sel (t : S.WorldType) : World := C.canon (w t)
  have hsec (t : S.WorldType) : S.toWorldType (sel t) = t :=
    canon_section_of_canon S C t (w t) (hw t)
  exact selector_of_lift S sel hsec

/-- The **selector induced by canonicalization** (using Choice for the
witness per type). When `canon` is internal, this selector can be
internal—see `internal_canon_implies_internal_selector` below. -/
noncomputable def selectorOfCanon (S : ObsSemantics World Obs) (C : Canonicalization S) : Selector S where
  sel t := C.canon (Classical.choose (canon_exists_rep S C t))
  sec t :=
    canon_section_of_canon S C t (Classical.choose (canon_exists_rep S C t))
      (Classical.choose_spec (canon_exists_rep S C t))

theorem selectorOfCanon_sec (t : S.WorldType) :
    S.toWorldType ((selectorOfCanon S C).sel t) = t :=
  (selectorOfCanon S C).sec t

/-! ## Internal canon ⇒ internal selector (nailed path) -/

section InternalCanon

variable [InternalPred (World → World)] [InternalPred (S.WorldType → World)]

/-- When the canonicalization map is **internal** (computable, definable, etc.),
the induced selector's underlying function can be built from `canon` plus
classical choice of a witness per type. In concrete internality models
(e.g. computable with effective enumeration), that construction is internal;
here we state the implication as an axiom/typeclass that downstream
instantiates. -/
class InternalCanonImpliesInternalSelector (S : ObsSemantics World Obs)
    [InternalPred (World → World)] [InternalPred (S.WorldType → World)] : Prop where
  /-- If `canon` is internal and forms a canonicalization, then some
      selector is internal (e.g. the one built from canon + effective choice). -/
  impl (C : Canonicalization S) (_hInternal : InternalPred.Internal C.canon) :
    ∃ sel : Selector S, SelectorInternal S sel

/-- **Internal canonicalization implies internal selector.**  Under
`InternalCanonImpliesInternalSelector`, an internal canon yields an
internal selector—the "nailed" U2 path via gauge-fixing. -/
theorem internal_canon_implies_internal_selector
    [InternalCanonImpliesInternalSelector S]
    (C : Canonicalization S) (hInternal : InternalPred.Internal C.canon) :
    ∃ sel : Selector S, SelectorInternal S sel :=
  InternalCanonImpliesInternalSelector.impl C hInternal

end InternalCanon

end Closure
