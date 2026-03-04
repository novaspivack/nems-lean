import NemS.Prelude
import SelfAwareness.Core.SelfModel

/-!
# SelfAwareness.Examples.ToyMultiplicity

**Two indistinguishable fixed points toy (Paper 33).**

Minimal witness that an update can have multiple fixed points: model state = Fin 2,
update = identity; then both 0 and 1 are fixed points. Used to illustrate selector
necessity when self-model multiplicity is present.
-/

set_option autoImplicit false

namespace SelfAwareness

/-- Toy self-model state: two possible states. -/
def toyModel := Fin 2

/-- Identity update: every state is a fixed point. -/
def toyUpdate (m : Fin 2) : Fin 2 := m

/-- Both elements of Fin 2 are fixed points of toyUpdate. -/
theorem toyUpdate_fix_zero : Fix toyUpdate (0 : Fin 2) := rfl

theorem toyUpdate_fix_one : Fix toyUpdate (1 : Fin 2) := rfl

/-- toyUpdate has multiple fixed points (at least two distinct). -/
theorem toy_multiple_fixed_points : MultipleFixedPoints toyUpdate := by
  refine ⟨(0 : Fin 2), (1 : Fin 2), by decide, rfl, rfl⟩

end SelfAwareness
