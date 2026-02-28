import NemS.Diagonal.ASR

/-!
# NemS.Diagonal.HaltingReduction

The halting reduction: if record-truth `RT` is computably decidable,
then the halting problem is computably decidable — contradiction.

This is the core engine of the diagonal barrier.  Given an ASR
structure (which bridges halting to record-truth), any total computable
decider for `RT` can be composed with the computable encoding to
produce a total computable halting decider.  But Mathlib's
`ComputablePred.halting_problem` says no such decider exists.
-/

namespace NemS
namespace Diagonal

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

/-- If `RT` is computably decidable and we have an ASR structure,
then the halting problem is computably decidable. -/
theorem asr_rt_computable_implies_halting_computable
    {F : Framework} (asr : ASR F) (hRT : ComputablePred asr.RT) :
    ∀ n, ComputablePred fun c => (eval c n).Dom := by
  intro n
  have : ComputablePred fun c => asr.RT (asr.encode c n) := by
    obtain ⟨hDec, hComp⟩ := hRT
    have hEnc : Computable fun c => asr.encode c n :=
      asr.encode_computable.comp Computable.id (Computable.const n)
    exact ⟨fun c => hDec (asr.encode c n), hComp.comp hEnc⟩
  exact this.of_eq (fun c => (asr.halts_iff_RT c n).symm)

/-- **The diagonal barrier (proved, not axiomatized).**

If a framework has an ASR structure, then record-truth `RT` is
NOT computably decidable.

Proof: if `RT` were computable, then by the ASR bridge, halting
would be computable.  But `ComputablePred.halting_problem` says
halting is not computable.  Contradiction. -/
theorem asr_rt_not_computable
    {F : Framework} (asr : ASR F) :
    ¬ ComputablePred asr.RT := by
  intro hRT
  have := asr_rt_computable_implies_halting_computable asr hRT 0
  exact ComputablePred.halting_problem 0 this

end Diagonal
end NemS
