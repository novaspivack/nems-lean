import NemS.Prelude
import Sieve.Core.Constraints
import Sieve.Theorems.Residual

/-!
# Sieve.Examples.ToyDomain

**Toy domain (Paper 34).**

A minimal theory space: candidates = Fin 3. Two constraints (e.g. "even index",
"nonzero"). Sieve = both. Certified residual contains a witness.
-/

set_option autoImplicit false

namespace Sieve

/-- Toy candidate space: three candidates. -/
def toySpace := Fin 3

/-- Constraint: "even" (0 and 2). -/
def toyC1 : Constraint (Fin 3) := fun i => (i : ℕ) % 2 = 0

/-- Constraint: "nonzero" (1 and 2). -/
def toyC2 : Constraint (Fin 3) := fun i => (i : ℕ) ≠ 0

/-- Sieve: both constraints. -/
def toySieve : List (Constraint (Fin 3)) := [toyC1, toyC2]

/-- Candidate 2 satisfies both: (2:ℕ)%2=0 and 2≠0. -/
theorem toy_residual_nonempty : ∃ a : Fin 3, SieveHolds (Fin 3) toySieve a := by
  refine ⟨2, ?_⟩
  simp only [SieveHolds, toySieve, toyC1, toyC2, List.forall_cons]
  exact ⟨rfl, ⟨by norm_num, trivial⟩⟩

end Sieve
