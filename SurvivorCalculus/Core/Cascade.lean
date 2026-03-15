import NemS.Prelude
import Sieve.Core.Constraints

/-!
# SurvivorCalculus.Core.Cascade

Generic cascade of predicates on a base space (Program III).
R_k = {x | C_1(x) ∧ ... ∧ C_k(x)}.
-/

set_option autoImplicit false

namespace SurvivorCalculus

variable (α : Type _)

/-- A cascade is a list of constraints (predicates) on α. -/
def Cascade := List (α → Prop)

/-- The residual class after the first k constraints: x satisfies all C_1,...,C_k. -/
def ResidualClass (cs : Cascade α) (k : ℕ) (x : α) : Prop :=
  Sieve.SieveHolds α (cs.take k) x

/-- Shorthand: x is in the full residual of the cascade. -/
def InResidual (cs : Cascade α) (x : α) : Prop :=
  Sieve.SieveHolds α cs x

end SurvivorCalculus
