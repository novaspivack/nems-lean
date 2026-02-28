import NemS.MFRR.PTSelector
import NemS.MFRR.DiagonalBarrier

/-!
# NemS.MFRR.PTNonEffective

Formally connects the diagonal barrier to the PT selector:
any PT that would constitute a total computable decider for
record-truth on the ASR fragment is ruled out.

This is the MFRR-aligned conclusion: "PT is lawful but
non-algorithmic on the self-referential record fragment."

## Key result

`pt_not_total_effective_on_RT`: given ASR, no internal selector
(PT) can serve as a total computable decider for RT.
-/

namespace NemS
namespace MFRR

open NemS.Framework
open NemS.Diagonal

/-- A PT is *total-effective on RT* if there exists a total computable
Boolean function that agrees with the ASR record-truth predicate
on all codes. -/
def PTTotalEffectiveOnRT
    {F : Framework} {IsInternal : F.Selector → Prop}
    (_pt : PT F IsInternal) (asr : ASR F) : Prop :=
  ComputablePred asr.RT

/-- **PT non-effectiveness theorem.**

In any diagonal-capable framework, no PT can be total-effective
on the ASR record-truth fragment.

This is the formal version of MFRR's claim that Transputation
is "lawful but non-algorithmic": the internal selector exists
(by the bridge theorem), but it cannot serve as a total computable
decider for record-truth on the self-referential fragment. -/
theorem pt_not_total_effective_on_RT
    {F : Framework} [dc : DiagonalCapable F]
    {IsInternal : F.Selector → Prop}
    (pt : PT F IsInternal) :
    ¬ PTTotalEffectiveOnRT pt dc.asr :=
  diagonal_barrier_rt F

/-- Combined: under PSC + choice + diagonal capability,
PT exists AND PT is not total-effective on RT. -/
theorem pt_exists_and_not_effective
    {F : Framework} [dc : DiagonalCapable F]
    {IsInternal : F.Selector → Prop}
    (hNEMS : NEMS F IsInternal)
    (hNC : ¬ F.ObsCategorical) :
    (∃ pt : PT F IsInternal, ¬ PTTotalEffectiveOnRT pt dc.asr) := by
  obtain ⟨S, hI⟩ := nems_noncat_implies_internal hNEMS hNC
  exact ⟨⟨S, hI⟩, pt_not_total_effective_on_RT ⟨S, hI⟩⟩

end MFRR
end NemS
