import Closure.Core.ObsSemantics
import Closure.Core.Selector

/-!
# Closure.Core.Effective

**Effective presentation** of observational semantics: enumeration of worlds
and decidability of observational equivalence. This is the minimal structure
needed to build selectors or canonicalizations *effectively* (e.g. computably),
so that the "internal outsourcing" theorem (U2) has a nontrivial instance.

* **EffectiveSemantics:** `ObsSemantics` plus `enum : Nat → World` (surjective)
  and decidability of `ObsEquiv`. With finite world-types (or bounded witness
  per type), a computable selector can be built by bounded search.
* **BoundedCover:** a natural number `cover` such that every world-type has a
  representative among `enum 0, ..., enum (cover-1)`. Enables bounded search for
  a representative per type (and hence a computable selector when combined
  with decidable equality on world-types).
* A concrete **computable** instance of `DeciderImpliesInternalSelector` or
  `InternalCanonImpliesInternalSelector` is provided in `Closure.Theorems.BoundedSelector`.
-/

set_option autoImplicit false

namespace Closure

universe u v

variable {World : Type u} {Obs : Type v}

/-- **Effective semantics:** observational semantics with an enumeration
of worlds and decidable observational equivalence. Enables effective
(e.g. computable) construction of a section: search for the least `n`
such that `toWorldType (enum n) = t`. Termination requires an extra
condition (e.g. finite world-types or bounded witness per type). -/
structure EffectiveSemantics (World : Type u) (Obs : Type v) where
  /-- The underlying observational semantics. -/
  semantics : ObsSemantics World Obs
  /-- Enumeration of worlds (not necessarily injective). -/
  enum : Nat → World
  /-- Every world appears in the enumeration. -/
  surj : ∀ w, ∃ n, enum n = w
  /-- Observational equivalence is decidable. -/
  decObsEquiv : DecidableRel semantics.ObsEquiv

namespace EffectiveSemantics

variable (E : EffectiveSemantics World Obs)

/-- Every world-type has at least one representative in the enumeration. -/
theorem exists_enum_rep (t : E.semantics.WorldType) :
    ∃ n : Nat, E.semantics.toWorldType (E.enum n) = t := by
  obtain ⟨w, hw⟩ := Quotient.exists_rep (s := E.semantics.obsEquivSetoid) t
  obtain ⟨n, rfl⟩ := E.surj w
  exact ⟨n, hw⟩

end EffectiveSemantics

/-- **Finite world-types:** the quotient has finitely many equivalence classes.
Under this and `EffectiveSemantics`, a selector can be built by bounded
search (find least `n` with `toWorldType (enum n) = t`). -/
def FiniteWorldTypes (S : ObsSemantics World Obs) : Prop :=
  Finite S.WorldType

/-- **Bounded cover** for an effective semantics: a bound `cover` such that
every world-type has at least one representative in `enum 0, ..., enum (cover-1)`.
This is the key assumption for building a selector by bounded search (see
`Closure.Theorems.BoundedSelector`). -/
structure BoundedCover (E : EffectiveSemantics World Obs) where
  cover : Nat
  cover_spec : ∀ t : E.semantics.WorldType,
    ∃ n : Nat, n < cover ∧ E.semantics.toWorldType (E.enum n) = t

end Closure
