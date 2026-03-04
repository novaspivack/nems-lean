import NemS.Prelude
import SelfAwareness.Theorems.IntrospectiveOptimality

/-!
# SelfAwareness.Examples.ToyRightness

**Stratified rightness (finite toy) (Paper 33).**

On a finite policy class and finite horizon, a total verifier for a rightness
predicate can exist (stratified positive result). Universal rightness certification
is impossible under diagonal capability (Theorems.IntrospectiveOptimality).
-/

set_option autoImplicit false

namespace SelfAwareness

/-- Finite policy type (e.g. Fin 2: two policies). -/
def toyPolicy := Fin 2

/-- Toy rightness: policy 0 is "right". -/
def toyRight (p : Fin 2) : Prop := p = 0

instance (p : Fin 2) : Decidable (toyRight p) := inferInstanceAs (Decidable (p = 0))

/-- **Stratified rightness toy:** on this finite policy class, a total verifier exists. -/
theorem stratified_rightness_toy :
    ∃ (δ : Fin 2 → Bool), ∀ p : Fin 2, (δ p = true ↔ toyRight p) := by
  refine ⟨fun p => decide (toyRight p), fun p => by rw [Bool.decide_iff]⟩

end SelfAwareness
