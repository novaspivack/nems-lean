import NemS.Diagonal.HaltingReduction
import NemS.Core.Internality

/-!
# NemS.Diagonal.Barrier

The diagonal barrier theorem: in any framework with an ASR structure,
no total-effective (computability-internal) selector can exist that
decides record-truth on all codes.

This replaces the axiom interface in `NemS.MFRR.DiagonalBarrier` with
a fully proved theorem, using the halting reduction from
`NemS.Diagonal.HaltingReduction`.

## Key result

`no_total_effective_rt_decider`: given ASR, record-truth is not
computably decidable.  This is the content of Theorem 5.9 of the
NEMS theorem paper, now machine-checked via Mathlib's halting
undecidability.
-/

namespace NemS
namespace Diagonal

open NemS.Framework

/-- **Theorem 5.9 analogue (fully proved).**

Given an ASR structure on framework `F`, the record-truth function
`RT` is not computably decidable.  This is the diagonal barrier:
any attempt to build a total effective selector that agrees with
record-truth on all codes would yield a halting decider. -/
theorem no_total_effective_rt_decider
    {F : Framework} (asr : ASR F) :
    ¬ ComputablePred asr.RT :=
  asr_rt_not_computable asr

end Diagonal
end NemS
