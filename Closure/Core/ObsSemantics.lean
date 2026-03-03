import NemS.Prelude

/-!
# Closure.Core.ObsSemantics

Generic observational semantics: worlds, observational propositions,
and observational equivalence.  Physics-agnostic; no NEMS-specific assumptions.

This is the A1 core layer for the Closure Calculus (theory closure / audit toolkit).
-/

set_option autoImplicit false

namespace Closure

universe u v

/-- Observational semantics: a type of worlds, a type of observational
propositions, and a satisfaction relation. -/
structure ObsSemantics (World : Type u) (Obs : Type v) where
  /-- `Holds w o` means observational proposition `o` holds in world `w`. -/
  Holds : World → Obs → Prop

variable {World : Type u} {Obs : Type v}

namespace ObsSemantics

variable (S : ObsSemantics World Obs)

/-- Two worlds are observationally equivalent iff they satisfy the same
observational propositions. -/
def ObsEquiv (w₁ w₂ : World) : Prop :=
  ∀ o : Obs, S.Holds w₁ o ↔ S.Holds w₂ o

namespace ObsEquiv

@[refl]
theorem refl (w : World) : S.ObsEquiv w w :=
  fun _ => Iff.rfl

@[symm]
theorem symm {w₁ w₂ : World} (h : S.ObsEquiv w₁ w₂) : S.ObsEquiv w₂ w₁ :=
  fun o => (h o).symm

@[trans]
theorem trans {w₁ w₂ w₃ : World} (h₁ : S.ObsEquiv w₁ w₂) (h₂ : S.ObsEquiv w₂ w₃) :
    S.ObsEquiv w₁ w₃ :=
  fun o => (h₁ o).trans (h₂ o)

/-- Observational equivalence is an equivalence relation. -/
theorem isEquivalence : Equivalence S.ObsEquiv :=
  ⟨refl S, symm S, trans S⟩

end ObsEquiv

/-- The setoid on `World` induced by observational equivalence. -/
def obsEquivSetoid : Setoid World where
  r     := S.ObsEquiv
  iseqv := ObsEquiv.isEquivalence S

/-- The quotient type of worlds by observational equivalence.
"World types" are the observational equivalence classes. -/
def WorldType : Type u :=
  Quotient S.obsEquivSetoid

/-- Canonical map from a world to its world-type. -/
def toWorldType (w : World) : S.WorldType :=
  Quotient.mk S.obsEquivSetoid w

/-- Two worlds have the same world-type iff they are observationally equivalent. -/
theorem toWorldType_eq_iff (w₁ w₂ : World) :
    S.toWorldType w₁ = S.toWorldType w₂ ↔ S.ObsEquiv w₁ w₂ :=
  Quotient.eq (r := S.obsEquivSetoid)

/-- A predicate on worlds is *observationally invariant* if it respects
observational equivalence. -/
def Invariant (P : World → Prop) : Prop :=
  ∀ {w₁ w₂ : World}, S.ObsEquiv w₁ w₂ → (P w₁ ↔ P w₂)

/-- Categorical: at most one world-type (all worlds are observationally equivalent). -/
def Categorical : Prop :=
  Subsingleton S.WorldType

/-- Needs selection: more than one world-type exists. -/
def NeedsSelection : Prop :=
  ¬ S.Categorical

end ObsSemantics

end Closure
