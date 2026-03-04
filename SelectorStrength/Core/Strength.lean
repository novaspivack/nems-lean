/-!
# SelectorStrength.Core.Strength


**Strength as a preorder of realizability classes (Paper 29).**

A strength level is a predicate on functions (e.g. deciders `α → Bool` or
transformers `α → α`). We define the preorder: S₁ ≤ S₂ iff every function
in S₁ is in S₂. Lattice structure (join/meet) is optional and can be added later.
-/

set_option autoImplicit false


namespace SelectorStrength

universe u v

/-! ## Strength as predicate on functions -/

/-- A **strength** (realizability class) on functions `α → β` is a predicate.
E.g. "computable", "all functions", "with k-bit advice". -/
def Strength (α : Type u) (β : Type v) : Type (max u v) := (α → β) → Prop

/-- **Weaker-or-equal**: S₁ ≤ S₂ iff every function in S₁ is in S₂. -/
def Strength.le {α β : Type _} (S₁ S₂ : Strength α β) : Prop :=
  ∀ f, S₁ f → S₂ f

/-- Preorder instance for Strength. -/
instance Strength.instLE (α β : Type _) : LE (Strength α β) where
  le := Strength.le

theorem Strength.le_refl {α β : Type _} (S : Strength α β) : S ≤ S := fun _ h => h

theorem Strength.le_trans {α β : Type _} {S₁ S₂ S₃ : Strength α β}
    (h12 : S₁ ≤ S₂) (h23 : S₂ ≤ S₃) : S₁ ≤ S₃ :=
  fun f h => h23 f (h12 f h)

end SelectorStrength
