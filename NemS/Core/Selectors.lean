import NemS.Core.ObsEq

/-!
# NemS.Core.Selectors

An internal selector is a canonical-representative functional on the
model space that:
1. Stays within the same observational equivalence class (selector-invariance).
2. Is idempotent (applying it twice gives the same result).
3. Is class-canonical (observationally equivalent models get the same image).

Internality is kept abstract: we parameterize by a predicate `IsInternal`
that downstream modules can instantiate.  For Phase 1 we prove purely
structural properties of selectors.
-/


namespace NemS

namespace Framework

variable (F : Framework)

/-- A `Selector` for framework `F` is a canonical-representative map on
`F.Model` that respects observational equivalence classes. -/
structure Selector where
  /-- The underlying map. -/
  sel  : F.Model → F.Model
  /-- The selected model is observationally equivalent to the input. -/
  inv  : ∀ M : F.Model, F.ObsEq (sel M) M
  /-- Applying the selector twice is the same as applying it once. -/
  idem : ∀ M : F.Model, sel (sel M) = sel M
  /-- Observationally equivalent inputs yield the same output. -/
  cong : ∀ {M N : F.Model}, F.ObsEq M N → sel M = sel N

namespace Selector

variable {F : Framework}

/-- The selector image is in the same world-type as the input. -/
theorem worldType_preserved (S : F.Selector) (M : F.Model) :
    F.toWorldType (S.sel M) = F.toWorldType M :=
  Quotient.sound (S.inv M)

/-- The selector is constant on each observational equivalence class. -/
theorem class_constant (S : F.Selector) {M N : F.Model}
    (h : F.ObsEq M N) : S.sel M = S.sel N :=
  S.cong h

/-- The image of the selector is a fixed point of the selector. -/
theorem image_fixed (S : F.Selector) (M : F.Model) :
    S.sel (S.sel M) = S.sel M :=
  S.idem M

/-- Two models in the same equivalence class have the same selector image. -/
theorem same_class_same_image (S : F.Selector) {M N : F.Model}
    (h : F.toWorldType M = F.toWorldType N) : S.sel M = S.sel N :=
  S.cong ((F.toWorldType_eq_iff).mp h)

end Selector

end Framework

end NemS
