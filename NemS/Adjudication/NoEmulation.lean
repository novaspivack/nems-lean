import NemS.Adjudication.Basic
import NemS.MFRR.DiagonalBarrier
import NemS.MFRR.PTNonEffective

/-!
# NemS.Adjudication.NoEmulation

**Paper 15 (C1): No-Emulation / Self-Necessitating Adjudication.**

This module proves that no total computable emulator can predict the
adjudication function (PT) on all inputs in a diagonal-capable framework.

## Proof strategy

The argument reduces to the diagonal barrier from `NemS.MFRR.DiagonalBarrier`:

1. Suppose an emulator `emu : F.Model → F.Model` exists and induces a
   computable decider for `RT` (i.e., `ComputablePred dc.asr.RT`).
2. But `diagonal_barrier_rt` asserts `¬ ComputablePred dc.asr.RT`.
3. Contradiction. Therefore no such emulator exists.

## Key results

- `no_emulation` : no emulator can induce a computable decider for RT.
- `adjudication_necessity` : no PT can be total-effective on RT.
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

/-- An emulator `emu` *induces a computable RT decider* if, via the ASR
encoding bridge, its action on the diagonal fragment yields a total computable
predicate for record-truth.

Formally: `ComputablePred dc.asr.RT` holds — i.e., there is a total computable
Boolean function on codes that decides `RT`. -/
def InducesComputableRT {F : Framework} [dc : DiagonalCapable F]
    {C : ChoicePointInterface F}
    (_adj : AdjudicationFn F C) (_emu : F.Model → F.Model) : Prop :=
  ComputablePred dc.asr.RT

/-- **No-Emulation Theorem (Paper 15).**

In any diagonal-capable framework, no emulator for an adjudication function
can induce a computable decider for record-truth `RT`.

Proof: `InducesComputableRT` is exactly `ComputablePred dc.asr.RT`, which is
refuted by `diagonal_barrier_rt`. -/
theorem no_emulation
    {F : Framework} [dc : DiagonalCapable F]
    {C : ChoicePointInterface F}
    (adj : AdjudicationFn F C)
    (emu : F.Model → F.Model) :
    ¬ InducesComputableRT adj emu :=
  diagonal_barrier_rt F

/-- **Adjudication Necessity (Paper 15, Corollary).**

No internal selector (PT) can be total-effective on record-truth.
Active internal selection is required and cannot be replaced by any
static algorithm. -/
theorem adjudication_necessity
    {F : Framework} [dc : DiagonalCapable F]
    {IsInternal : F.Selector → Prop}
    (pt : PT F IsInternal) :
    ¬ PTTotalEffectiveOnRT pt dc.asr :=
  pt_not_total_effective_on_RT pt

end Adjudication
end NemS
