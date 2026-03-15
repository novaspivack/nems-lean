import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import Hypercomputation.Core.HypercomputerClaim
import Hypercomputation.Theorems.NoInternalHypercomputer
import NemS.Diagonal.QuotientSectionStrength

open SelectorStrength
open NemS.Diagonal
open Encodable Denumerable
open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

/-!
# Hypercomputation.Examples.Halting

**Halting predicate example (Paper 35).**

Wraps the halting-framework no-decider theorem in the Hypercomputation
interface. No internal total hypercomputer exists for the "halts on input 0"
predicate at computable strength.
-/

set_option autoImplicit false

namespace Hypercomputation
namespace Examples

/-- Computable strength on ℕ → Bool: δ is in the class iff Computable δ. -/
def S_computable_halting : Strength ℕ Bool := fun δ => Computable δ

/-- **No internal hypercomputer for halting (Paper 35).**

No computable total decider exists for the halts-on-zero predicate.
This is the classic halting undecidability, packaged in Paper 35 vocabulary. -/
theorem no_internal_hypercomputer_for_halting :
    ¬ HasInternalHypercomputerAt S_computable_halting haltsOnZero := by
  intro h
  obtain ⟨δ, hS, hDec⟩ := h
  exact halting_framework_no_decider_at_computable ⟨δ, hS, hDec⟩

/-- **No total computable halting hypercomputer.** Alias. -/
theorem no_total_computable_halting_hypercomputer :
    ¬ HasInternalHypercomputerAt S_computable_halting haltsOnZero :=
  no_internal_hypercomputer_for_halting

end Examples
end Hypercomputation
