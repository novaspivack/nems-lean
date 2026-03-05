import SemanticNonlocality.Core.LocalityAxioms
import Closure.Core.ObsSemantics

/-!
# SemanticNonlocality.Theorems.LocalDynamicsNotLocalSemantics

**Paper 45: Local dynamics do not imply local semantics.**

When Holds factorizes, world-type (observational equivalence class) is determined
by the *global* local-view map: w ↦ (f ↦ restrict w f). Same local views ⇒ same
world-type; semantics is "glued" globally.
-/

set_option autoImplicit false

namespace SemanticNonlocality

variable {World : Type*} {Obs : Type*} (S : Closure.ObsSemantics World Obs) (L : LocalityAxioms S)

open Closure.ObsSemantics

/-- Same local views imply same world-type (global gluing). -/
theorem same_local_views_imp_same_world_type
    (w₁ w₂ : World) (h : ∀ f : L.Fragment, L.restrict w₁ f = L.restrict w₂ f) :
    S.toWorldType w₁ = S.toWorldType w₂ :=
  S.toWorldType_eq_iff w₁ w₂ |>.mpr (same_local_views_imp_obs_equiv S L w₁ w₂ h)

end SemanticNonlocality
