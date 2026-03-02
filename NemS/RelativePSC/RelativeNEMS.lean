import NemS.RelativePSC.FrameworkA
import NemS.Core.Trichotomy
import NemS.MFRR.PSCBundle
import NemS.ReverseBICS.BICS_Implies_NEMS

/-!
# NemS.RelativePSC.RelativeNEMS

**Paper 16 (C2): Relative NEMS and Recursive Closure.**

This module defines `RelativeNEMS` and the `RelativePSCBundle` for a subsystem.
It proves the core recursion principle (T16.1): if a subsystem implements
BICS-like complete internal semantics for its own records, it inherits NEMS.

## Key definitions

- `RelativeNEMS` : NEMS applied to the subsystem's framework.
- `RelativePSCBundle` : The combination of RelativeNEMS and DeterminacyPSC
  for the subsystem.

## Key results

- `recursive_nems` : BICS on subsystem A implies RelativeNEMS for A.
-/

namespace NemS
namespace RelativePSC

open NemS.Framework
open NemS.MFRR
open NemS.ReverseBICS

/-- Relative NEMS: the subsystem's framework satisfies NEMS.
This means no external selector (outside subsystem A) is load-bearing
for A's record determinacy. -/
def RelativeNEMS {F : Framework} (A : Subsystem F)
    (IsInternal_A : A.toFramework.Selector → Prop) : Prop :=
  NEMS A.toFramework IsInternal_A

/-- Relative PSC Bundle: the conjunction of Relative NEMS and
DeterminacyPSC for subsystem A. -/
structure RelativePSCBundle {F : Framework} (A : Subsystem F)
    (IsInternal_A : A.toFramework.Selector → Prop) where
  /-- The subsystem satisfies NEMS. -/
  nems : RelativeNEMS A IsInternal_A
  /-- The subsystem satisfies DeterminacyPSC. -/
  detPSC : A.toFramework.DeterminacyPSC

/-- **Recursive NEMS Theorem (Paper 16, T16.1).**

If subsystem A implements BICS-like complete internal semantics for its
own records, then A satisfies Relative NEMS.

This establishes the "fractal closure" of the NEMS framework: any subsystem
that achieves semantic closure internally becomes a NEMS domain, regardless
of its embedding in the parent framework. -/
theorem recursive_nems {F : Framework} (A : Subsystem F)
    (IsInternal_A : A.toFramework.Selector → Prop)
    (hBICS : BICS A.toFramework) :
    RelativeNEMS A IsInternal_A :=
  bics_implies_nems hBICS IsInternal_A

end RelativePSC
end NemS
