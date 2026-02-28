import NemS.Core.Categoricity
import NemS.Core.ObsEq

/-!
# NemS.MFRR.ChoicePoints

Abstract choice-point interface for the MFRR bridge.

A *choice point* in MFRR is a configuration where the local deterministic
rules underdetermine the next state: multiple record-consistent continuations
exist.  This module formalizes that notion abstractly on top of the NEMS
`Framework` and proves that genuine choice (≥ 2 distinct record-consistent
branches) implies non-categoricity — the key bridge lemma connecting MFRR's
physics vocabulary to the NEMS classification spine.
-/

namespace NemS
namespace MFRR

open NemS.Framework

variable {F : Framework}

/-- A `ChoiceData` for framework `F` packages:
- A type of *choice-point labels* for each model,
- A *branch set* for each choice point (the admissible continuations),
- Evidence that the branch set is always nonempty. -/
structure ChoiceData (F : Framework) where
  /-- The type of choice-point labels available at a given model. -/
  CP : F.Model → Type
  /-- The set of admissible branches (continuations) at a choice point. -/
  branches : {M : F.Model} → CP M → Set F.Model
  /-- Every choice point has at least one branch. -/
  nonempty : ∀ {M : F.Model} (c : CP M), (branches c).Nonempty

/-- A branch is *record-consistent* with the originating model if they are
observationally equivalent (agree on all record statements). -/
def branchConsistent (F : Framework) (M b : F.Model) : Prop :=
  F.ObsEq M b

/-- `HasGenuineChoice` asserts that the framework admits at least one
choice point with two distinct branches that are both record-consistent
with the originating model.  This is the abstract formalization of
MFRR's "the local rules underdetermine the continuation." -/
def HasGenuineChoice (F : Framework) (cd : ChoiceData F) : Prop :=
  ∃ (M : F.Model) (c : cd.CP M) (b₁ b₂ : F.Model),
    b₁ ∈ cd.branches c ∧ b₂ ∈ cd.branches c ∧
    b₁ ≠ b₂ ∧
    branchConsistent F M b₁ ∧ branchConsistent F M b₂

/-- Genuine choice with *record-divergent* branches: two branches at
some choice point that disagree on at least one record statement.
This is the operationally meaningful notion: the choice point produces
branches with genuinely different observational content. -/
def HasRecordDivergentChoice (F : Framework) (cd : ChoiceData F) : Prop :=
  ∃ (M : F.Model) (c : cd.CP M) (b₁ b₂ : F.Model),
    b₁ ∈ cd.branches c ∧ b₂ ∈ cd.branches c ∧
    ¬ F.ObsEq b₁ b₂

/-- Record-divergent choice implies non-categoricity. -/
theorem recordDivergentChoice_implies_not_obsCategorical
    (cd : ChoiceData F)
    (h : HasRecordDivergentChoice F cd) :
    ¬ F.ObsCategorical := by
  obtain ⟨_M, _c, b₁, b₂, _, _, hne⟩ := h
  intro hcat
  exact hne (hcat b₁ b₂)

/-- Convenience: if we already know non-categoricity from choice data,
we can extract the witness in the form needed by `not_obsCategorical_iff`. -/
theorem recordDivergentChoice_witness
    (cd : ChoiceData F)
    (h : HasRecordDivergentChoice F cd) :
    ∃ M N : F.Model, ∃ r : F.Rec,
      (F.Truth M r ∧ ¬ F.Truth N r) ∨ (¬ F.Truth M r ∧ F.Truth N r) := by
  have hNC := recordDivergentChoice_implies_not_obsCategorical cd h
  exact (F.not_obsCategorical_iff).mp hNC

end MFRR
end NemS
