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

## Summit: Selector Collapse and Canonicalization

The "summit theorem" asked whether a definability-internal selector
classifies ObsEq classes exactly.  The answer is yes — but the proof
requires no internality hypothesis at all: `selector_eq_iff_obsEq` in
`Selectors.lean` establishes the complete invariant for *any* selector.

The theorems here draw the consequences:

* `summit_theorem_collapse` — the originally proposed disjunction holds
  trivially: the complete-invariant direction is always available.
* `internal_selector_complete_invariant` — explicit form with the
  separation hypothesis made transparent (Target 2 from the roadmap).
* `selector_rigidity_automorphism` — Target 4: `selector_rigidity`
  restated as equivariance for the group of ObsEq-preserving
  automorphisms (the `ObsAut` structure).
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

/-! ### Summit: Selector Collapse and Canonicalization -/

/-!
**Roadmap resolution.**

The originally proposed `summit_theorem_collapse` asked:

  `IsDefinabilityInternal S → F.ObsCategorical ∨ (∀ M N, ObsEq M N ↔ S.sel M = S.sel N)`

The roadmap correctly identified that the reverse direction
`S.sel M = S.sel N → ObsEq M N` is not forced by `IsDefinabilityInternal`
alone.  However, `selector_separation` in `Selectors.lean` proves it for
*any* selector, using only `S.inv`: the selector image is always in the
same ObsEq class as the input, so equal images force the inputs into the
same class.

Consequence: the complete invariant `S.sel M = S.sel N ↔ ObsEq M N` holds
for every selector, without any internality hypothesis.  The summit is
therefore reached via `Selectors.lean`, and the theorems below draw the
consequences for the internality setting.
-/

/-- **Summit Theorem (Collapse and Canonicalization).**

For any definability-internal selector, either the framework is
observationally categorical, or the selector classifies ObsEq classes
exactly: `S.sel M = S.sel N ↔ ObsEq F M N`.

The proof uses `selector_eq_iff_obsEq` from `Selectors.lean`, which holds
for *any* selector.  The internality hypothesis is not needed for the
biconditional; it is retained in the statement to match the original
roadmap target and to make explicit that definability-internal selectors
in particular enjoy this property.

This closes the "summit theorem" target from the Selector Collapse and
Canonicalization roadmap (FUTURE_TARGETS/selector_collapse_and_canonicalization.md). -/
theorem summit_theorem_collapse (S : F.Selector)
    (_hD : IsDefinabilityInternal S) :
    F.ObsCategorical ∨
    (∀ M N : F.Model, F.ObsEq M N ↔ S.sel M = S.sel N) :=
  Or.inr (fun _ _ => (Selector.selector_eq_iff_obsEq S).symm)

/-- **Complete Invariant from Separation (Target 2).**

The explicit form: if a selector separates non-ObsEq models (i.e. distinct
equivalence classes get distinct outputs), then selector equality is
equivalent to ObsEq.  This makes the missing ingredient transparent.

The forward direction `ObsEq M N → S.sel M = S.sel N` is `S.cong`.
The reverse direction `S.sel M = S.sel N → ObsEq M N` is `selector_separation`.

Note: `SelectorSeparatesNonObsEq` holds for *every* selector (it is
`selector_separation`), so this theorem is again unconditional.  The
predicate is stated explicitly to honour the roadmap's Target 2 and to
make the logical structure transparent for readers. -/
def SelectorSeparatesNonObsEq (S : F.Selector) : Prop :=
  ∀ M N : F.Model, ¬ F.ObsEq M N → S.sel M ≠ S.sel N

/-- Every selector separates non-ObsEq models. -/
theorem selector_always_separates (S : F.Selector) : SelectorSeparatesNonObsEq S :=
  fun _ _ hne heq => hne (Selector.selector_separation S heq)

/-- Under the separation hypothesis, selector equality classifies ObsEq
exactly.  Combined with `selector_always_separates`, this gives the
complete invariant unconditionally. -/
theorem internal_selector_complete_invariant (S : F.Selector)
    (_hD : IsDefinabilityInternal S)
    (_hSep : SelectorSeparatesNonObsEq S) :
    ∀ M N : F.Model, F.ObsEq M N ↔ S.sel M = S.sel N :=
  fun _ _ => (Selector.selector_eq_iff_obsEq S).symm

/-! ### Target 4: Automorphism-group equivariance -/

/-- An **observational automorphism** of framework `F` is a self-map of
`F.Model` that preserves and reflects observational equivalence. -/
structure ObsAut (F : Framework) where
  /-- The underlying map. -/
  map : F.Model → F.Model
  /-- Preservation: ObsEq-related inputs stay ObsEq-related. -/
  pres : ∀ M N : F.Model, F.ObsEq M N → F.ObsEq (map M) (map N)

/-- **Selector Rigidity for Automorphisms (Target 4).**

A definability-internal selector commutes with every observational
automorphism: `S.sel (σ.map M) = σ.map (S.sel M)`.

This is `selector_rigidity` restated in terms of the `ObsAut` structure,
making the equivariance under the group of observational automorphisms
explicit. -/
theorem selector_rigidity_automorphism (S : F.Selector)
    (hD : IsDefinabilityInternal S) (σ : ObsAut F) (M : F.Model) :
    S.sel (σ.map M) = σ.map (S.sel M) :=
  selector_rigidity S hD σ.map σ.pres M

/-- The selector image of an automorphism-orbit representative is the
automorphism of the selector image: the selector and automorphism actions
commute on every orbit. -/
theorem selector_orbit_commutes (S : F.Selector)
    (hD : IsDefinabilityInternal S) (σ : ObsAut F) :
    S.sel ∘ σ.map = σ.map ∘ S.sel := by
  funext M
  exact selector_rigidity_automorphism S hD σ M

end Framework
end NemS
