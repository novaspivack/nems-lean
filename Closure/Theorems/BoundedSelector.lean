import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Basic
import Closure.Core.ObsSemantics
import Closure.Core.Selector
import Closure.Core.Effective
import Closure.Core.Canonicalization

/-!
# Closure.Theorems.BoundedSelector

**Nailed instance:** under effective semantics with a **bounded cover** and
canonicalization, we build a selector in two layers.

1. **Classical (existence):** `BoundedCover E` + `Canonicalization E.semantics` →
   `Nonempty (Selector E.semantics)` via `repOfType t = enum (choose (cover_spec t))`
   and `sel t = canon (repOfType t)`. Uses `Classical.choose`; definitions are
   marked `noncomputable`.

2. **Total / constructive (bounded search):** When we have a **decidable membership
   test** for "enum n has world-type t"—i.e. the predicate
   `fun n => toWorldType (enum n) = t` is decidable—we can build a selector
   without Choice by bounded search. We assume `[DecidableEq E.semantics.WorldType]`,
   which provides that test (compare quotient elements). The construction is
   **total** (no `Classical.choose`) and **constructive**; the representative
   is `enum (min' of indices n < cover with toWorldType (enum n) = t)`, then
   `sel t = canon (findRepBounded t)`. For formal **computability** in the
   recursion-theory sense (e.g. `Computable sel`) one would additionally need
   `Computable enum`, `Computable canon`, and the decidability to be
   computably realized; we do not assume that here.

3. **Toy instance:** See `Closure.Examples.FintypeWorld`: when `[Fintype World]`
   and decidable `ObsEquiv`, we get `EffectiveSemantics` and `BoundedCover`;
   then the bounded-search selector applies.
-/

set_option autoImplicit false

namespace Closure

universe u v

variable {World : Type u} {Obs : Type v}

/-! ## General: selector from bounded cover + canonicalization (classical) -/

section Classical

variable (E : EffectiveSemantics World Obs) (bc : BoundedCover E)
  (C : Canonicalization E.semantics)

/-- A representative world for type `t` (classical: uses choice from cover_spec). -/
noncomputable def repOfTypeClassical (t : E.semantics.WorldType) : World :=
  E.enum (Classical.choose (bc.cover_spec t))

theorem repOfTypeClassical_spec (t : E.semantics.WorldType) :
    E.semantics.toWorldType (repOfTypeClassical E bc t) = t :=
  (Classical.choose_spec (bc.cover_spec t)).2

/-- Selector built from bounded cover and canonicalization (classical). -/
noncomputable def boundedSelectorClassical : Selector E.semantics where
  sel t := C.canon (repOfTypeClassical E bc t)
  sec t := canon_section_of_canon E.semantics C t (repOfTypeClassical E bc t) (repOfTypeClassical_spec E bc t)

/-- Under bounded cover and canonicalization, a selector exists. -/
theorem nonempty_selector_of_bounded_cover (E : EffectiveSemantics World Obs) (bc : BoundedCover E)
    (C : Canonicalization E.semantics) :
    Nonempty (Selector E.semantics) :=
  ⟨boundedSelectorClassical E bc C⟩

end Classical

/-! ## Total selector by bounded search (decidable membership) -/

section BoundedSearch

variable (E : EffectiveSemantics World Obs) (bc : BoundedCover E)
  (C : Canonicalization E.semantics)
  [DecidableEq E.semantics.WorldType]

/-- The set of indices `n < cover` such that `enum n` has world-type `t`.
    Membership is decidable because we have `[DecidableEq E.semantics.WorldType]`:
    the test is `toWorldType (enum n) = t`. -/
def repIndices (t : E.semantics.WorldType) : Finset Nat :=
  (Finset.range bc.cover).filter fun n => E.semantics.toWorldType (E.enum n) = t

theorem repIndices_nonempty (t : E.semantics.WorldType) :
    (repIndices E bc t).Nonempty := by
  obtain ⟨n, hn, heq⟩ := bc.cover_spec t
  exact ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, heq⟩⟩

/-- Representative for type `t` as the world at the minimal index in `repIndices t`.
    Total and constructive (no `Classical.choose`). For formal `Computable` in the
    recursion-theory sense, additionally assume `Computable enum` and `Computable canon`. -/
def findRepBounded (t : E.semantics.WorldType) : World :=
  E.enum ((repIndices E bc t).min' (repIndices_nonempty E bc t))

theorem findRepBounded_spec (t : E.semantics.WorldType) :
    E.semantics.toWorldType (findRepBounded E bc t) = t := by
  have h := (repIndices E bc t).min'_mem (repIndices_nonempty E bc t)
  simp only [repIndices, Finset.mem_filter] at h
  exact h.2

/-- Selector built by bounded search. Total (no Choice); decidable equality on
    world-types provides the membership test used in the search. -/
def boundedSelector (t : E.semantics.WorldType) : World :=
  C.canon (findRepBounded E bc t)

theorem boundedSelector_sec (t : E.semantics.WorldType) :
    E.semantics.toWorldType (boundedSelector E bc C t) = t :=
  canon_section_of_canon E.semantics C t (findRepBounded E bc t) (findRepBounded_spec E bc t)

/-- The bounded-search construction yields a selector (total, no Choice). -/
def boundedSelectorAsSelector : Selector E.semantics where
  sel := boundedSelector E bc C
  sec := boundedSelector_sec E bc C

end BoundedSearch

end Closure
