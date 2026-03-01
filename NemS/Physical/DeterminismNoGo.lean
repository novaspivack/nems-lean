import NemS.Physical.ASRFromUCT
import NemS.Diagonal.Barrier

/-!
# NemS.Physical.DeterminismNoGo

Determinism no-go theorem: in diagonal-capable frameworks, no total
effective deterministic law can decide all record-truth questions on
the diagonal fragment.

This is a corollary of the diagonal barrier, packaged as a statement
about determinism.
-/

namespace NemS
namespace Physical

open NemS.Diagonal

/-- **Determinism no-go theorem.**

If a framework is diagonal-capable (carries ASR or PhysUCT), then
there is no total computable function that decides record-truth on
all codes in the ASR fragment.

This is the "determinism no-go" form of the diagonal barrier:
any purported total effective deterministic record-truth decider
contradicts the halting undecidability. -/
theorem diagonal_forbids_total_determinism
    {F : Framework} (asr : ASR F) :
    ¬ ComputablePred asr.RT :=
  no_total_effective_rt_decider asr

/-- Corollary: PhysUCT forbids total-effective record determinism. -/
theorem physUCT_forbids_total_determinism
    {F : Framework} (uct : PhysUCT F) :
    ¬ ComputablePred uct.RT :=
  diagonal_forbids_total_determinism (physUCT_implies_ASR uct)

end Physical
end NemS
