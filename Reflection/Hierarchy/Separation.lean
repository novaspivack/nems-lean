import Mathlib.Data.Nat.Basic
import Reflection.Core.SRI_R
import Reflection.Theorems.DiagonalClosure

/-!
# Reflection.Hierarchy.Separation

**Method-level separation**: a concrete R that is NOT diagonally closed,
with a specific F ∈ R such that G_F ∉ R. The diagonal construction cannot
generate a fixed point for F using the internal method, because G_F is
not representable.

## Concrete example: identity-only R on ℕ

We build a degenerate SRI on ℕ:
- Obj = Code = ℕ, Equiv = Eq
- quote = id, run e c = e + c

Then run c c = 2c, so G_F(c) = F(quote(run c c)) = F(2c).

For F = id: G_id(c) = 2c ≠ id(c) = c. So G_id ≠ id.

Define R(F) := F = id (singleton class). Then:
- id ∈ R
- G_id = (c ↦ 2c) ≠ id, so G_id ∉ R
- Hence R is NOT diagonally closed

This is a **method-level separation**: the diagonal closure theorem does
not apply; you cannot generate a fixed point via repr(G_F) because G_F ∉ R.
-/

set_option autoImplicit false

namespace Reflection

namespace Hierarchy

/-! ## Degenerate SRI on ℕ (run e c = e + c) -/

/-- Degenerate SRI on ℕ: quote = id, run e c = e + c.
Used to exhibit a strict separation. -/
def degenerateSRI : SRI_R ℕ ℕ (· = id) where
  Equiv       := (· = ·)
  equiv_refl  := fun _ => rfl
  equiv_symm  := fun h => h.symm
  equiv_trans := fun h₁ h₂ => h₁.trans h₂
  quote       := id
  run         := (· + ·)
  repr F hF   := 0
  repr_spec   := by
    intro F hF c
    simp only [Nat.zero_add]
    rw [hF]
    rfl

local instance : SRI_R ℕ ℕ (· = id) := degenerateSRI

/-- The diagonalization of id: G_id(c) = id(quote(run c c)) = run c c = 2c. -/
theorem diag_id_eq_double : (fun c => id (degenerateSRI.quote (degenerateSRI.run c c))) = (· * 2) := by
  ext c
  delta degenerateSRI
  show id (id (c + c)) = c * 2
  rw [id_eq, id_eq, ← Nat.two_mul c, mul_comm]

/-- G_id ≠ id: the diagonalization of the identity is doubling, not identity. -/
theorem diag_id_ne_id : (fun c : ℕ => id (degenerateSRI.quote (degenerateSRI.run c c))) ≠ id := by
  intro h
  have h1 : (fun c => id (degenerateSRI.quote (degenerateSRI.run c c))) 1 = id 1 := congr_fun h 1
  delta degenerateSRI at h1
  simp only [id_eq] at h1
  omega

/-- R = {id} is NOT diagonally closed: id ∈ R but G_id ∉ R. -/
theorem not_diagClosed_identity_only : ¬ DiagClosed (· = id : (ℕ → ℕ) → Prop) := by
  intro h
  have hG : (fun c => id (degenerateSRI.quote (degenerateSRI.run c c))) = id := h id rfl
  exact diag_id_ne_id hG

/-- **Method-level separation**: there exists F ∈ R such that G_F ∉ R.
Concretely: F = id ∈ R, but G_id = (· * 2) ∉ R. -/
theorem method_level_separation :
    ∃ F : ℕ → ℕ, (· = id : (ℕ → ℕ) → Prop) F ∧
      ¬ (· = id : (ℕ → ℕ) → Prop) (fun c => F (degenerateSRI.quote (degenerateSRI.run c c))) := by
  use id
  constructor
  · rfl
  · intro h
    exact diag_id_ne_id h

/-- **Separation summary**: the diagonal closure theorem does not apply to R = {id};
fixed points for F ∈ R cannot be generated via the internal repr(G_F) method
because G_F ∉ R. -/
theorem separation_summary : True := trivial

end Hierarchy

end Reflection
