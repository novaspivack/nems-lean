import NemS.Prelude
import SelfAwareness.Core.ClaimFamilies

/-!
# SelfAwareness.Examples.ToyHierarchy

**Toy claim ladder (Paper 33).**

Finite claim type (e.g. Fin n) with decidable semantics: base class C0 has
a total certifier constructively. C2 is blocked by the barrier (see Theorems.Hierarchy).
-/

set_option autoImplicit false

namespace SelfAwareness

variable (n : ℕ) [NeZero n]

/-- Toy claim type: Fin n. -/
def toyClaims := Fin n

/-- Decidable semantics on Fin n (e.g. arbitrary Bool). -/
def toySem (i : Fin n) : Prop := (i : ℕ) % 2 = 0

instance (i : Fin n) : Decidable (toySem n i) := inferInstanceAs (Decidable ((i : ℕ) % 2 = 0))

/-- Base class C0: all claims (finite). Total certifier exists: decide toySem. -/
theorem base_certifier_exists :
    ∃ (δ : Fin n → Bool), ∀ i : Fin n, (δ i = true ↔ toySem n i) := by
  refine ⟨fun i => decide (toySem n i), fun i => by simp only [Bool.decide_iff]⟩

end SelfAwareness
