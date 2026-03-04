import NemS.Prelude

/-!
# SelfAwareness.Core.SelfModel

**Self-model update and fixed points (Paper 33).**

SelfModel type, Update operator, fixed-point set. Multiplicity = at least two distinct fixed points.
-/

set_option autoImplicit false

namespace SelfAwareness

/-- Self-model state type. -/
def SelfModel := Type

/-- Update operator on self-model states. -/
def Update (M : Type) := M → M

/-- Fixed points of an update: Fix U = { m | U m = m }. -/
def Fix {M : Type} (U : M → M) (m : M) : Prop := U m = m

/-- Multiple fixed points: at least two distinct m₁, m₂ with U m₁ = m₁ and U m₂ = m₂. -/
def MultipleFixedPoints {M : Type} (U : M → M) : Prop :=
  ∃ m₁ m₂ : M, m₁ ≠ m₂ ∧ U m₁ = m₁ ∧ U m₂ = m₂

end SelfAwareness
