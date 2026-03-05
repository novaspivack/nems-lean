import Closure.Core.ObsSemantics

/-!
# HolographyUnderClosure.Core.Semantics

**Paper 48: Bulk and boundary observational semantics.**

We work with two observational semantics: **bulk** (World₁, Obs₁, S₁) and
**boundary** (World₂, Obs₂, S₂). Holography is a closure-preserving
interpretation between them (see Interpretation.lean). No spacetime structure;
purely algebraic.
-/

set_option autoImplicit false

namespace HolographyUnderClosure

universe u v

/-- **Bulk/boundary setup**: two observational semantics. Bulk = "interior",
boundary = "boundary" (e.g. CFT side). Interpretation will map boundary → bulk. -/
structure BulkBoundarySemantics
    (World₁ : Type u) (Obs₁ : Type v) (World₂ : Type u) (Obs₂ : Type v) where
  bulk : Closure.ObsSemantics World₁ Obs₁
  boundary : Closure.ObsSemantics World₂ Obs₂

end HolographyUnderClosure
