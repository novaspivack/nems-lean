import NemS.Prelude
import Sieve.Core.TheorySpace

/-!
# Sieve.Core.Constraints

**Constraints and sieve (Paper 34).**

Constraint = predicate on α. Sieve = conjunction of a list of constraints.
Residual = subtype of α satisfying the sieve.
-/

set_option autoImplicit false

namespace Sieve

variable (α : Type _)

/-- A constraint on candidates is a predicate. -/
def Constraint := α → Prop

/-- Sieve: conjunction of constraints (list). A candidate satisfies the sieve iff
it satisfies every constraint in the list. -/
def SieveHolds (cs : List (Constraint α)) (a : α) : Prop :=
  cs.Forall (fun C => C a)

/-- Residual: subtype of α whose elements satisfy the sieve. -/
def Residual (cs : List (Constraint α)) : Type _ :=
  { a : α // SieveHolds α cs a }

theorem sieve_nil (a : α) : SieveHolds α [] a := by
  simp [SieveHolds]

theorem sieve_cons (C : Constraint α) (cs : List (Constraint α)) (a : α) :
    SieveHolds α (C :: cs) a ↔ C a ∧ SieveHolds α cs a := by
  simp [SieveHolds]

end Sieve
