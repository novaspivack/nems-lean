import Reflection.Core.SRI_R

/-!
# Reflection.Theorems.DiagonalClosure

## The Diagonal Closure Theorem (restricted fixed points)

**Theorem** (`restricted_master_fixed_point`): If `R` is diagonally closed,
then every `F ∈ R` has a mixed fixed point: ∃ p, p ≃ F(quote p).

Proof: Set `G_F(c) := F(quote(run c c))`. By DiagClosed, `R G_F`.
So we have `d := repr G_F hG : Code`. Let `p := run d d`.
By repr_spec: `run d d ≃ G_F d = F(quote(run d d)) = F(quote p)`.
Thus `p ≃ F(quote p)`.

This is the headline theorem of Paper 28 — Reflection as a Resource.
-/

set_option autoImplicit false

namespace Reflection

universe u v

variable {Obj : Type u} {Code : Type v} {R : (Code → Obj) → Prop}
  [S : SRI_R Obj Code R]

/-- **Diagonal Closure Theorem (restricted fixed points).**

If `R` is closed under the diagonalization template, then every `F ∈ R`
has a mixed fixed point: ∃ p : Obj, p ≃ F(quote p).

This quantifies "how much internalization is enough": diagonally closed
classes get fixed points for all their members. -/
theorem restricted_master_fixed_point (hDiag : DiagClosed R) (F : Code → Obj) (hF : R F) :
    ∃ p : Obj, S.Equiv p (F (S.quote p)) := by
  let G : Code → Obj := fun c => F (S.quote (S.run c c))
  have hG : R G := hDiag F hF
  let d := S.repr G hG
  use S.run d d
  exact S.repr_spec G hG d

/-- **Escape-hatch corollary**: if `R` is *not* diagonally closed, then
either (a) exhibit an `F ∈ R` without a fixed point (separation), or
(b) fixed points exist only for a proper subclass.

We state the positive direction: when DiagClosed holds, fixed points exist. -/
theorem fixed_points_iff_diag_closed (hDiag : DiagClosed R) (F : Code → Obj) (hF : R F) :
    ∃ p : Obj, S.Equiv p (F (S.quote p)) :=
  restricted_master_fixed_point hDiag F hF

end Reflection
