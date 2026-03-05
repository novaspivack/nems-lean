import Closure.Core.ObsSemantics

/-!
# SemanticNonlocality.Core.LocalityAxioms

**Paper 45: Locality as factorization of Holds.**

Locality axioms are defined at the Holds level: global Holds factors over local
fragments (restrict world to each fragment, local predicate per fragment).
Not geometric—purely algebraic factorization.
-/

set_option autoImplicit false

namespace SemanticNonlocality

universe u v w

variable {World : Type u} {Obs : Type v}

open Closure.ObsSemantics

/-- **Locality structure**: observational semantics plus factorization data. -/
structure LocalityAxioms (S : Closure.ObsSemantics World Obs) where
  /-- Index type for local fragments. -/
  Fragment : Type w
  /-- Type of world restricted to a fragment. -/
  LocalWorld : Type w
  /-- Restriction of world to a fragment. -/
  restrict : World → Fragment → LocalWorld
  /-- Local predicate at a fragment. -/
  localHolds : Fragment → LocalWorld → Obs → Prop
  /-- Global Holds factors as conjunction over fragments. -/
  factorized : ∀ w o, S.Holds w o ↔ ∀ f : Fragment, localHolds f (restrict w f) o

variable (S : Closure.ObsSemantics World Obs) (L : LocalityAxioms S)

/-- **Factorized** (proposition): the locality structure satisfies factorization. -/
def Factorized : Prop :=
  ∀ w o, S.Holds w o ↔ ∀ f : L.Fragment, L.localHolds f (L.restrict w f) o

theorem factorized_holds : Factorized S L :=
  L.factorized

/-- When factorized, same local views imply observational equivalence. -/
theorem same_local_views_imp_obs_equiv
    (w₁ w₂ : World) (h : ∀ f : L.Fragment, L.restrict w₁ f = L.restrict w₂ f) :
    S.ObsEquiv w₁ w₂ := by
  intro o
  constructor
  · intro h1; rw [factorized_holds S L w₂ o]; intro f; rw [← h f]; exact (L.factorized w₁ o).mp h1 f
  · intro h2; rw [factorized_holds S L w₁ o]; intro f; rw [h f]; exact (L.factorized w₂ o).mp h2 f

end SemanticNonlocality
