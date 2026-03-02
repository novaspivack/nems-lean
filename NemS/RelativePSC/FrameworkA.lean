import NemS.Core.Basics

/-!
# NemS.RelativePSC.FrameworkA

**Paper 16 (C2): Relative PSC and Recursive NEMS.**

This module defines the concept of a "subsystem framework" $F_A$.
A subsystem defines its own internal model, records, and truth relation,
which can be formally treated as a `Framework` in its own right.

## Key definitions

- `Subsystem F` : A subsystem $A$ within a parent framework $F$, specifying
  its own internal model, records, and truth.
- `Subsystem.toFramework` : The projection of a subsystem into a standard
  `Framework` object, allowing all NEMS theorems to apply to it.
-/

namespace NemS
namespace RelativePSC

open NemS.Framework

/-- A subsystem $A$ within a parent framework $F$.
It defines its own internal model, records, and truth relation. -/
structure Subsystem (F : Framework) where
  /-- The internal state space of subsystem A. -/
  Model_A : Type
  /-- The internal record space of subsystem A. -/
  Rec_A : Type
  /-- The internal truth relation for subsystem A. -/
  Truth_A : Model_A → Rec_A → Prop

/-- Any subsystem can be viewed as a standalone framework.
This allows us to apply the entire NEMS machinery (BICS, Diagonal Barrier, etc.)
directly to the subsystem. -/
def Subsystem.toFramework {F : Framework} (A : Subsystem F) : Framework :=
  { Model := A.Model_A,
    Rec   := A.Rec_A,
    Truth := A.Truth_A }

/-- A boundary channel $C_{out}$ represents external selection data injected
into subsystem $A$ that is not representable in $A$'s internal records.
In the relative NEMS context, this corresponds to external selectors. -/
structure BoundaryChannel {F : Framework} (A : Subsystem F) where
  /-- The type of external selection signals. -/
  C_out : Type
  /-- How external signals affect the subsystem's state transitions. -/
  inject : C_out → A.Model_A → A.Model_A

end RelativePSC
end NemS
