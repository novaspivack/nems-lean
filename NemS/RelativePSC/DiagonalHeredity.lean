import NemS.RelativePSC.RelativeNEMS
import NemS.MFRR.DiagonalBarrier
import NemS.Adjudication.NoEmulation

/-!
# NemS.RelativePSC.DiagonalHeredity

**Paper 16 (C2): Heredity of the Diagonal Barrier.**

This module proves that if a subsystem $A$ is rich enough to host Arithmetic
Self-Reference (i.e., it is `DiagonalCapable`), then the diagonal barrier and
the necessity of internal adjudication apply directly to $A$, independently
of the parent framework.

## Key results

- `diagonal_heredity` : T16.2. The diagonal barrier applies to subsystem A.
- `relative_adjudication_necessity` : Adjudication within A cannot be total-effective.
-/

namespace NemS
namespace RelativePSC

open NemS.Framework
open NemS.MFRR
open NemS.Diagonal
open NemS.Adjudication

/-- **Heredity of the Diagonal Barrier (Paper 16, T16.2).**

If subsystem A is diagonal-capable (can host ASR internally), then its
internal record-truth is not computably decidable. -/
theorem diagonal_heredity {F : Framework} (A : Subsystem F)
    [dc_A : DiagonalCapable A.toFramework] :
    ¬ ComputablePred dc_A.asr.RT :=
  diagonal_barrier_rt A.toFramework

/-- **Relative Adjudication Necessity.**

Consequent to the diagonal heredity, any internal adjudication function (PT)
operating within subsystem A cannot be total-effective on A's diagonal fragment. -/
theorem relative_adjudication_necessity {F : Framework} (A : Subsystem F)
    [dc_A : DiagonalCapable A.toFramework]
    {IsInternal_A : A.toFramework.Selector → Prop}
    (pt_A : PT A.toFramework IsInternal_A) :
    ¬ PTTotalEffectiveOnRT pt_A dc_A.asr :=
  pt_not_total_effective_on_RT pt_A

end RelativePSC
end NemS
