import NemS.Core.SelectorQuotient
import NemS.Core.Internality
import NemS.Diagonal.ASR
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Basic

/-!
# NemS.Core.QuotientSection

## Internal realizability of quotient sections

A *quotient section* is a right inverse of `toWorldType`:
`q : WorldTypes F → F.Model` with `∀ wt, toWorldType F (q wt) = wt`.

The selector–quotient splitting (`selectorSectionEquiv`) established that
selectors and quotient sections are the same structure. Classification is
settled. The sharp question: **when is the quotient section internally
realizable** — computably, definably, or by bounded search?

This module defines:
- `IsQuotientSection` — the section property
- `EffectivePresentation` — enum + decidability (Framework-specific)
- `BoundedCover` — bound such that every world-type has a rep in enum 0..(cover-1)
- `IsComputablyRealizedSection` — section built by bounded search (no Choice)
- `IsDefinablyRealizedSection` — section whose induced selector is definability-internal
- Theorems: bounded cover gives computable section, section⇔selector internality
-/

namespace NemS

namespace Framework

variable (F : Framework)

/-! ### Program 1: Core definitions -/

/-- A function `q` is a **quotient section** for `F` if it is a right inverse
of `toWorldType`: applying `toWorldType` to `q wt` returns `wt`. -/
def IsQuotientSection (q : F.WorldTypes → F.Model) : Prop :=
  ∀ wt : F.WorldTypes, F.toWorldType (q wt) = wt

/-- **Effective presentation** of a framework: an enumeration of models that
hits every world-type, plus decidability of observational equivalence.
Enables bounded search for a representative per world-type. -/
structure EffectivePresentation where
  enum : Nat → F.Model
  surj : ∀ M : F.Model, ∃ n : Nat, F.ObsEq (enum n) M
  decObsEq : DecidableRel F.ObsEq

/-- **Bounded cover** for an effective presentation: a natural bound such that
every world-type has at least one representative among `enum 0, ..., enum (cover - 1)`.
This is the key assumption for building a section by bounded search. -/
structure BoundedCover (ep : EffectivePresentation F) where
  cover : Nat
  cover_spec : ∀ wt : F.WorldTypes,
    ∃ n : Nat, n < cover ∧ F.toWorldType (ep.enum n) = wt

variable {F}

/-! ### Section from bounded cover (constructive, no Choice) -/

section BoundedSearch

variable (ep : EffectivePresentation F) (bc : BoundedCover F ep)
  [DecidableEq F.WorldTypes]

/-- The set of indices `n < cover` such that `enum n` has world-type `t`. -/
def repIndices (t : F.WorldTypes) : Finset Nat :=
  (Finset.range bc.cover).filter fun n => F.toWorldType (ep.enum n) = t

theorem repIndices_nonempty (t : F.WorldTypes) :
    (repIndices ep bc t).Nonempty := by
  obtain ⟨n, hn, heq⟩ := bc.cover_spec t
  exact ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, heq⟩⟩

/-- Representative for world-type `t` as the model at the minimal index.
Total and constructive (no `Classical.choose`). -/
def findRepBounded (t : F.WorldTypes) : F.Model :=
  ep.enum ((repIndices ep bc t).min' (repIndices_nonempty ep bc t))

theorem findRepBounded_spec (t : F.WorldTypes) :
    F.toWorldType (findRepBounded ep bc t) = t := by
  have h := (repIndices ep bc t).min'_mem (repIndices_nonempty ep bc t)
  simp only [repIndices, Finset.mem_filter] at h
  exact h.2

/-- **Quotient section built by bounded search.** Total, no Choice.
This is the computably realizable section. -/
def sectionFromBoundedCover (t : F.WorldTypes) : F.Model :=
  findRepBounded ep bc t

theorem sectionFromBoundedCover_spec (t : F.WorldTypes) :
    F.toWorldType (sectionFromBoundedCover ep bc t) = t :=
  findRepBounded_spec ep bc t

/-- The bounded-search construction yields a quotient section. -/
theorem isQuotientSection_sectionFromBoundedCover :
    IsQuotientSection F (sectionFromBoundedCover ep bc) :=
  sectionFromBoundedCover_spec ep bc

end BoundedSearch

/-! ### Computably and definably realized sections -/

/-- A quotient section is **computably realizable** if it can be built from
an effective presentation with bounded cover and decidable world-type equality.
Precisely: there exist `ep`, `bc`, and `[DecidableEq F.WorldTypes]` such that
`q` equals the section built by bounded search.

We use a structure to carry the witness data rather than an existential,
so downstream can use the effective presentation when needed. -/
structure ComputablyRealizedSection (q : F.WorldTypes → F.Model) where
  ep : EffectivePresentation F
  bc : BoundedCover F ep
  decWt : DecidableEq F.WorldTypes
  eq_section : q = sectionFromBoundedCover ep bc

/-- A quotient section is computably realizable iff it admits the structure. -/
def IsComputablyRealizedSection (q : F.WorldTypes → F.Model) : Prop :=
  Nonempty (ComputablyRealizedSection q)

/-- A quotient section is **definably realizable** if the induced selector
(`quotientSectionToSelector q hsec`) is definability-internal. -/
def IsDefinablyRealizedSection (q : F.WorldTypes → F.Model)
    (hsec : IsQuotientSection F q) : Prop :=
  IsDefinabilityInternal (quotientSectionToSelector q hsec)

/-! ### Program 2: Bounded cover gives computable section (Target A) -/

/-- **Bounded cover gives computable quotient section.**

Under effective presentation + bounded cover + decidable world-type equality,
there exists a computably realizable quotient section. The section is
built by bounded search; no Choice is used. -/
theorem bounded_cover_gives_computable_quotient_section
    (ep : EffectivePresentation F) (bc : BoundedCover F ep)
    [DecidableEq F.WorldTypes] :
    ∃ q : F.WorldTypes → F.Model,
      IsQuotientSection F q ∧ IsComputablyRealizedSection q := by
  use sectionFromBoundedCover ep bc
  constructor
  · exact isQuotientSection_sectionFromBoundedCover ep bc
  · exact ⟨⟨ep, bc, inferInstance, rfl⟩⟩

/-! ### Program 3: Section ⇔ Selector internality (Target C) -/

/-- **Computable section implies computable selector (Target C, forward).**

A computably realizable quotient section induces a selector that satisfies
`IsComputabilityInternal` (factors through the quotient via a section). -/
theorem computable_section_implies_computable_selector
    (q : F.WorldTypes → F.Model) (_hsec : IsQuotientSection F q)
    (hComp : IsComputablyRealizedSection q) :
    ∃ S : F.Selector, IsComputabilityInternal S := by
  obtain ⟨crs⟩ := hComp
  haveI : DecidableEq F.WorldTypes := crs.decWt
  let q' := sectionFromBoundedCover crs.ep crs.bc
  have hsec' : IsQuotientSection F q' := isQuotientSection_sectionFromBoundedCover crs.ep crs.bc
  let S := quotientSectionToSelector q' hsec'
  refine ⟨S, ?_, ?_⟩
  · use q'
    intro M; rfl
  · use q'
    intro wt; exact hsec' wt

/-- **Effective structure gives both (Target C, reverse).**

Under effective presentation + bounded cover + decidable world-types,
there exists both a computably realizable section and a selector with
`IsComputabilityInternal`. They are related by `selectorSectionEquiv`. -/
theorem effective_structure_gives_computable_selector
    (ep : EffectivePresentation F) (bc : BoundedCover F ep)
    [DecidableEq F.WorldTypes] :
    ∃ S : F.Selector, IsComputabilityInternal S := by
  obtain ⟨q, hsec, hComp⟩ := bounded_cover_gives_computable_quotient_section ep bc
  exact computable_section_implies_computable_selector q hsec hComp

/-- **Definable section iff definable selector (Target C).**

A quotient section is definably realizable iff the induced selector is
definability-internal. This is an equivalence because the section and
selector determine each other uniquely via `selectorSectionEquiv`. -/
theorem definable_section_iff_definable_selector (q : F.WorldTypes → F.Model)
    (hsec : IsQuotientSection F q) :
    IsDefinablyRealizedSection q hsec ↔
    IsDefinabilityInternal (quotientSectionToSelector q hsec) :=
  Iff.rfl

/-! ### Program 4: Exact criterion (Target D) -/

/-- Witness structure for the exact criterion: effective presentation +
bounded cover + decidable world-types. -/
structure EffectiveQuotientSectionStructure (F : Framework) where
  ep : EffectivePresentation F
  bc : BoundedCover F ep
  decWt : DecidableEq F.WorldTypes

/-- **Exact criterion for computable sections (Target D).**

A quotient section is computably realizable iff the framework admits
effective presentation with bounded cover and decidable world-type equality.

Forward: by definition of `ComputablyRealizedSection`.
Reverse: `bounded_cover_gives_computable_quotient_section`. -/
theorem exact_criterion_computable_section :
    (∃ q : F.WorldTypes → F.Model,
      IsQuotientSection F q ∧ IsComputablyRealizedSection q) ↔
    Nonempty (EffectiveQuotientSectionStructure F) := by
  constructor
  · rintro ⟨_q, _hsec, ⟨crs⟩⟩
    exact ⟨⟨crs.ep, crs.bc, crs.decWt⟩⟩
  · rintro ⟨⟨ep, bc, decWt⟩⟩
    haveI : DecidableEq F.WorldTypes := decWt
    exact bounded_cover_gives_computable_quotient_section ep bc

/-! ### Program 5: Diagonal obstruction (Target E) -/

/-- **Unbounded world-types:** for every natural `n`, the framework has at least
`n + 1` pairwise observationally distinct models. Diagonal-capable frameworks
(e.g. the halting framework with ASR) satisfy this: distinct halting patterns
yield distinct world-types. -/
def UnboundedWorldTypes (F : Framework) : Prop :=
  ∀ n : Nat, ∃ m : Fin (n + 1) → F.Model,
    ∀ i j, i ≠ j → ¬ F.ObsEq (m i) (m j)

/-- **Total-effective quotient section:** a section that is realizable by a
total effective procedure. Under diagonal capability, such a section cannot
exist on the record fragment — that would contradict the diagonal barrier.

Precise formulation: when the framework has ASR (diagonal-capable) and
unbounded world-types, no quotient section can be both (a) a valid section
and (b) total-effective in the sense of computable realizability.

Proof: A computably realizable section requires EffectiveQuotientSectionStructure
(EffectivePresentation + BoundedCover with finite `cover`). The cover_spec
implies at most `cover` distinct world-types. UnboundedWorldTypes with
`n = cover` yields `cover + 1` pairwise distinct world-types. Contradiction.
See Paper 02. -/
theorem no_total_effective_quotient_section_on_diagonal_fragment
    (_asr : NemS.Diagonal.ASR F) (hub : UnboundedWorldTypes F)
    (q : F.WorldTypes → F.Model) (_hsec : IsQuotientSection F q) :
    ¬ IsComputablyRealizedSection q := by
  intro hComp
  obtain ⟨crs⟩ := hComp
  haveI : DecidableEq F.WorldTypes := crs.decWt
  obtain ⟨m, hDistinct⟩ := hub crs.bc.cover
  have hCover : ∀ wt, ∃ n, n < crs.bc.cover ∧ F.toWorldType (crs.ep.enum n) = wt := crs.bc.cover_spec
  let wts : Finset F.WorldTypes :=
    (Finset.univ : Finset (Fin (crs.bc.cover + 1))).image fun i => F.toWorldType (m i)
  have hSub : wts ⊆ (Finset.range crs.bc.cover).image fun n => F.toWorldType (crs.ep.enum n) := by
    intro wt hwt
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hwt
    obtain ⟨n, hn, heq⟩ := hCover (F.toWorldType (m i))
    exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, heq⟩
  have hImgCard : ((Finset.range crs.bc.cover).image fun n => F.toWorldType (crs.ep.enum n)).card ≤
      (Finset.range crs.bc.cover).card := Finset.card_image_le
  have hRangeCard : (Finset.range crs.bc.cover).card = crs.bc.cover := Finset.card_range crs.bc.cover
  have hRightSize : ((Finset.range crs.bc.cover).image fun n => F.toWorldType (crs.ep.enum n)).card ≤
      crs.bc.cover := hImgCard.trans_eq hRangeCard
  have hCard : wts.card ≤ crs.bc.cover := (Finset.card_le_card hSub).trans hRightSize
  have hCard' : wts.card = crs.bc.cover + 1 := by
    rw [Finset.card_image_of_injective (Finset.univ : Finset (Fin (crs.bc.cover + 1)))]
    · exact Finset.card_fin (crs.bc.cover + 1)
    · intro i j heq
      by_contra hne
      exact hDistinct i j hne ((F.toWorldType_eq_iff).mp heq)
  rw [hCard'] at hCard
  omega

end Framework

end NemS
