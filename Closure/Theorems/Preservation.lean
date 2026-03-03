import Closure.Core.Internal
import Closure.Core.Selector

/-!
# Closure.Theorems.Preservation

Closure preservation under morphisms: reducts, definitional extensions,
interpretations (U3).  High-value theorems:

1. Interpretation preserves invariants (pullback).
2. Categoricity preservation: surjective worldMap + target categorical ⇒ source categorical.
3. Selector transport: target selector + right inverse on world-types ⇒ source selector.
-/

set_option autoImplicit false

namespace Closure

universe u v

/-- An **interpretation** from one observational semantics to another:
maps worlds and observations in a satisfaction-preserving way. -/
structure Interpretation
    (World₁ : Type u) (Obs₁ : Type v) (S₁ : ObsSemantics World₁ Obs₁)
    (World₂ : Type u) (Obs₂ : Type v) (S₂ : ObsSemantics World₂ Obs₂) where
  /-- Map worlds of the target back to the source (reduct direction). -/
  worldMap : World₂ → World₁
  /-- Map observational propositions from source to target. -/
  obsMap : Obs₁ → Obs₂
  /-- Satisfaction is preserved: `S₁.Holds (worldMap w) o ↔ S₂.Holds w (obsMap o)`. -/
  holds : ∀ w₂ o₁, S₁.Holds (worldMap w₂) o₁ ↔ S₂.Holds w₂ (obsMap o₁)

variable {World₁ World₂ : Type u} {Obs₁ Obs₂ : Type v}
  (S₁ : ObsSemantics World₁ Obs₁) (S₂ : ObsSemantics World₂ Obs₂)

/-- Under an interpretation, observational equivalence is preserved
(in the reduct direction). -/
theorem Interpretation.obsEquiv_preserved
    (I : Interpretation World₁ Obs₁ S₁ World₂ Obs₂ S₂)
    (w₂₁ w₂₂ : World₂) (h : S₂.ObsEquiv w₂₁ w₂₂) :
    S₁.ObsEquiv (I.worldMap w₂₁) (I.worldMap w₂₂) := by
  intro o₁
  rw [I.holds, I.holds]
  exact h (I.obsMap o₁)

/-! ## 1. Invariant preservation (pullback) -/

/-- **Interpretation preserves invariants.**  If `Q` is invariant in the
source semantics `S₁`, then the pullback `Q ∘ I.worldMap` is invariant
in the target semantics `S₂`. -/
theorem Interpretation.invariant_preserved
    (I : Interpretation World₁ Obs₁ S₁ World₂ Obs₂ S₂)
    (Q : World₁ → Prop) (hQ : S₁.Invariant Q) :
    S₂.Invariant (Q ∘ I.worldMap) := by
  intro w₂₁ w₂₂ h
  show (Q ∘ I.worldMap) w₂₁ ↔ (Q ∘ I.worldMap) w₂₂
  simp only [Function.comp_apply]
  have hobs : S₁.ObsEquiv (I.worldMap w₂₁) (I.worldMap w₂₂) := fun o₁ =>
    (I.holds w₂₁ o₁).trans ((h (I.obsMap o₁)).trans (I.holds w₂₂ o₁).symm)
  exact hQ hobs

/-! ## 2. Categoricity preservation -/

/-- **WorldMap surjective on world-types:** every source world-type is
the image of some target world under worldMap. -/
def Interpretation.surjectiveOnWorldTypes
    (I : Interpretation World₁ Obs₁ S₁ World₂ Obs₂ S₂) : Prop :=
  ∀ t₁ : S₁.WorldType, ∃ w₂ : World₂, S₁.toWorldType (I.worldMap w₂) = t₁

/-- **Categoricity preservation.**  If the target `S₂` is categorical and
worldMap is surjective on world-types, then the source `S₁` is categorical. -/
theorem Interpretation.categoricity_preserved
    (I : Interpretation World₁ Obs₁ S₁ World₂ Obs₂ S₂)
    (hSurj : I.surjectiveOnWorldTypes)
    (hCat : S₂.Categorical) :
    S₁.Categorical :=
  ⟨fun t₁₁ t₁₂ => by
    obtain ⟨w₂₁, heq₁⟩ := hSurj t₁₁
    obtain ⟨w₂₂, heq₂⟩ := hSurj t₁₂
    have heq : S₂.toWorldType w₂₁ = S₂.toWorldType w₂₂ :=
      @Subsingleton.allEq S₂.WorldType hCat (S₂.toWorldType w₂₁) (S₂.toWorldType w₂₂)
    have hobs : S₂.ObsEquiv w₂₁ w₂₂ := (S₂.toWorldType_eq_iff w₂₁ w₂₂).mp heq
    have hobs₁ : S₁.ObsEquiv (I.worldMap w₂₁) (I.worldMap w₂₂) := fun o₁ =>
      (I.holds w₂₁ o₁).trans ((hobs (I.obsMap o₁)).trans (I.holds w₂₂ o₁).symm)
    rw [← heq₁, ← heq₂]
    exact (Quotient.eq (r := S₁.obsEquivSetoid)).mpr hobs₁
  ⟩

/-! ## 3. Selector transport -/

/-- A **right inverse on world-types** for an interpretation and a target
selector: for each source world-type `t₁`, `r t₁` is a target world-type
such that mapping the selected target world back to the source has type `t₁`. -/
def Interpretation.rightInverseOnWorldTypes
    (I : Interpretation World₁ Obs₁ S₁ World₂ Obs₂ S₂)
    (sel₂ : Selector S₂) (r : S₁.WorldType → S₂.WorldType) : Prop :=
  ∀ t₁, S₁.toWorldType (I.worldMap (sel₂.sel (r t₁))) = t₁

/-- **Selector transport.**  Given an interpretation, a selector for the
target, and a right inverse on world-types (i.e. `I.rightInverseOnWorldTypes sel₂ r`),
we obtain a selector for the source. -/
theorem Interpretation.selector_transport
    (I : Interpretation World₁ Obs₁ S₁ World₂ Obs₂ S₂)
    (sel₂ : Selector S₂)
    (r : S₁.WorldType → S₂.WorldType)
    (hr : ∀ t₁, S₁.toWorldType (I.worldMap (sel₂.sel (r t₁))) = t₁) :
    Nonempty (Selector S₁) := by
  let sel₁ : S₁.WorldType → World₁ := fun t₁ => I.worldMap (sel₂.sel (r t₁))
  exact selector_of_lift S₁ sel₁ hr

end Closure
