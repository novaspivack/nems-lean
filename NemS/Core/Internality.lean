import NemS.Core.Trichotomy

/-!
# NemS.Core.Internality

Two concrete instantiations of the abstract `IsInternal` predicate,
demonstrating that the framework is robust under different notions of
"internal."

## Instantiation 1: Definability-style internality
A selector is internal if it is uniquely determined by the framework
structure and invariant under automorphisms preserving ObsEq.

## Instantiation 2: Computability-style internality
A selector is internal if it factors through a computable section of
the quotient map (a decidable canonical-representative function on
equivalence classes).
-/

namespace NemS
namespace Framework

variable {F : Framework}

/-! ### Instantiation 1: Definability-style internality -/

/-- A selector is *definability-internal* if it is uniquely determined
by the framework structure and invariant under ObsEq-preserving maps. -/
def IsDefinabilityInternal (S : Selector F) : Prop :=
  (∀ S' : Selector F, (∀ M : F.Model, S.sel M = S'.sel M) → S = S') ∧
  (∀ (σ : F.Model → F.Model),
    (∀ M N : F.Model, ObsEq F M N → ObsEq F (σ M) (σ N)) →
    ∀ M : F.Model, S.sel (σ M) = σ (S.sel M))

/--
A definability-internal selector is rigid under any self-map of the model space
that preserves observational equivalence: applying the selector after such a map
agrees with mapping the selector's output.

This is an exported interface lemma for the automorphism-invariance component of
`IsDefinabilityInternal`.
-/
theorem selector_rigidity (S : F.Selector)
    (hD : IsDefinabilityInternal S) (σ : F.Model → F.Model)
    (hσ : ∀ M N : F.Model, ObsEq F M N → ObsEq F (σ M) (σ N))
    (M : F.Model) :
    S.sel (σ M) = σ (S.sel M) :=
  hD.2 σ hσ M

/-- Under definability-internality, NEMS means: either categorical, or
there exists a unique, invariant selector. -/
theorem nems_definability (h : NEMS F IsDefinabilityInternal) :
    F.ObsCategorical ∨ ∃ S : Selector F, IsDefinabilityInternal S :=
  nems_implies_cat_or_internal h

/-! ### Instantiation 2: Computability-style internality -/

/-- A selector is *computability-internal* if it factors through the
quotient: there exists a section `q` on world-types such that
`S.sel M = q [M]` for all `M`, and the section lands in the correct
equivalence class. -/
def IsComputabilityInternal (S : Selector F) : Prop :=
  (∃ q : Quotient (obsEqSetoid F) → F.Model,
    ∀ M : F.Model, S.sel M = q (toWorldType F M)) ∧
  (∃ q : Quotient (obsEqSetoid F) → F.Model,
    ∀ wt : Quotient (obsEqSetoid F), toWorldType F (q wt) = wt)

/-- Under computability-internality, NEMS means: either categorical, or
there exists a computable selector. -/
theorem nems_computability (h : NEMS F IsComputabilityInternal) :
    F.ObsCategorical ∨ ∃ S : Selector F, IsComputabilityInternal S :=
  nems_implies_cat_or_internal h

/-- Definability-internal selectors admit a quotient section
(the first half of computability-internality). -/
theorem definability_implies_quotient_section
    (S : Selector F) (_hD : IsDefinabilityInternal S) :
    ∃ q : Quotient (obsEqSetoid F) → F.Model,
      ∀ M : F.Model, S.sel M = q (toWorldType F M) := by
  refine ⟨Quotient.lift S.sel (fun M N h => S.cong h), ?_⟩
  intro M
  rfl

end Framework
end NemS
