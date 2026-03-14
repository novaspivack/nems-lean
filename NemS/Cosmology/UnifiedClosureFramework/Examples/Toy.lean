import NemS.Cosmology.UnifiedClosureFramework
import NemS.Examples.Toy

/-!
# NemS.Cosmology.UnifiedClosureFramework.Examples.Toy

**Toy witness: UnifiedClosureFramework is inhabited.**

Builds a UnifiedClosureFramework from the Bool framework (NemS.Examples.Toy)
with trivial visibility (all records visible at all times). This demonstrates
the structure is nonvacuous.

Note: A full CosmologicalClosureSchema witness would require a framework with
DiagonalCapable, Universe, and PSCBundle. The Bool framework has PSCBundle
(NemS.MFRR.ToyMFRR) but lacks DiagonalCapable. A full witness would need a
diagonal-capable framework (e.g. haltingFramework from NemS.Physical.Instantiation)
with PSCBundle; that construction is follow-on work.
-/

set_option autoImplicit false

namespace NemS
namespace Cosmology
namespace UnifiedClosureFramework
namespace Examples

open NemS.Examples

/-- Trivial visibility: every record is visible at every time. -/
def trivialVisible (_t : Nat) (_r : Bool) : Prop := True

/-- Trivial visibility is monotone. -/
theorem trivialVisible_mono (t t' : Nat) (r : Bool) (_hle : t ≤ t') (_hv : trivialVisible t r) :
    trivialVisible t' r := trivial

/-- Toy UnifiedClosureFramework built from the Bool framework. -/
def toyUnified : UnifiedClosureFramework where
  World := Bool
  Rec := Bool
  Truth := fun M r => M = r
  InitState := Unit
  init := ()
  Visible := trivialVisible
  visible_mono := trivialVisible_mono

/-- The toy projects to the Bool framework. -/
theorem toy_toFramework : toyUnified.toFramework = boolFramework := rfl

/-- **Structural nonvacuity:** UnifiedClosureFramework is inhabited. -/
theorem unified_framework_inhabited : Nonempty (UnifiedClosureFramework.{0, 0, 0}) :=
  ⟨toyUnified⟩

end Examples
end UnifiedClosureFramework
end Cosmology
end NemS
