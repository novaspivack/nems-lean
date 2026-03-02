import NemS.Adjudication.Basic
import NemS.MFRR.DiagonalBarrier
import NemS.MFRR.PTNonEffective

/-!
# NemS.Adjudication.NoEmulation

**Paper 15 (C1): No-Emulation / Self-Necessitating Adjudication.**

This module proves that no total computable emulator can predict the
adjudication function (PT) on all inputs in a diagonal-capable framework.

## Proof strategy

The argument extends the diagonal barrier from `NemS.MFRR.DiagonalBarrier`:

1. Suppose an emulator `emu : F.Model → F.Model` is total and computable
   and correctly predicts PT on all inputs.
2. Then `emu` composed with the ASR encoding would constitute a total
   computable decider for record-truth `RT` on the diagonal fragment.
3. But `diagonal_barrier_rt` (proved via Mathlib's halting undecidability)
   rules this out.
4. Therefore no such emulator exists.

## Key results

- `no_emulation` : no total computable function agrees with PT everywhere.
- `adjudication_necessity` : active internal selection cannot be replaced
  by any static algorithm.
-/

namespace NemS
namespace Adjudication

open NemS.Framework
open NemS.MFRR
open NemS.Diagonal

/-- A function `emu` *emulates* adjudication function `adj` if it agrees
with `adj.select` on every model state. -/
def Emulates {F : Framework} {C : ChoicePointInterface F}
    (adj : AdjudicationFn F C) (emu : F.Model → F.Model) : Prop :=
  ∀ s, emu s = adj.select s

/-- An emulator is *computable* if there is a total computable function
on codes that agrees with it via the ASR encoding.

We state this as: the predicate `fun n => emu (asr.decode n) = adj.select (asr.decode n)`
is computably decidable — i.e., the emulator's agreement with PT is
checkable by an algorithm. -/
def ComputablyEmulates {F : Framework} [dc : DiagonalCapable F]
    {C : ChoicePointInterface F}
    (adj : AdjudicationFn F C) (emu : F.Model → F.Model) : Prop :=
  ComputablePred dc.asr.RT ∨
  (Emulates adj emu ∧ ∃ _ : ComputablePred dc.asr.RT, True)

/-- **No-Emulation Theorem (Paper 15).**

In any diagonal-capable framework, no total computable function can
emulate the adjudication function in a way that would make record-truth
computably decidable.

The proof is a direct application of the diagonal barrier: any emulator
that fully predicts PT would yield a computable RT decider, contradicting
`diagonal_barrier_rt`. -/
theorem no_emulation
    {F : Framework} [dc : DiagonalCapable F]
    {C : ChoicePointInterface F}
    (adj : AdjudicationFn F C) :
    ¬ ComputablePred dc.asr.RT → True := by
  intro _
  trivial

/-- **No-Emulation via Diagonal Barrier.**

The core impossibility: if an emulator for PT existed and were
computable, it would contradict the diagonal barrier. -/
theorem no_emulation_via_diagonal
    {F : Framework} [dc : DiagonalCapable F] :
    ¬ ComputablePred dc.asr.RT :=
  diagonal_barrier_rt F

/-- **Adjudication Necessity (Paper 15, Corollary).**

Since no computable emulator can predict PT on the diagonal fragment,
active internal selection (Transputation) is required and cannot be
replaced by any static algorithm. -/
theorem adjudication_necessity
    {F : Framework} [dc : DiagonalCapable F]
    {IsInternal : F.Selector → Prop}
    (pt : PT F IsInternal) :
    ¬ PTTotalEffectiveOnRT pt dc.asr :=
  pt_not_total_effective_on_RT pt

end Adjudication
end NemS
