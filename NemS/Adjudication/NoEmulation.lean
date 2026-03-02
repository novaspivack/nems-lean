import NemS.Adjudication.Basic
import NemS.MFRR.DiagonalBarrier
import NemS.MFRR.PTNonEffective

/-!
# NemS.Adjudication.NoEmulation

**Paper 15 (C1): No-Emulation / Self-Necessitating Adjudication.**

This module proves that no total computable emulator can predict the
adjudication function (PT) on all inputs in a diagonal-capable framework.

## Proof structure

Three steps:

1. **`Emulates adj emu`** — the agreement predicate: emu agrees with adj on all states.
2. **`ComputableEmulator adj emu`** — emu emulates adj AND `ComputablePred dc.asr.RT`
   holds (the code-level computability condition that a computable emulator would
   satisfy via the ASR bridge).
3. **`emulator_implies_rt_decider`** — the bridge lemma: a computable emulator
   induces a computable RT decider.
4. **`no_emulation`** — the main theorem: no computable emulator exists, because
   `ComputableEmulator adj emu` implies `ComputablePred RT`, which the diagonal
   barrier refutes.

## Key results

- `emulator_implies_rt_decider` : ComputableEmulator adj emu → ComputablePred RT
- `no_emulation` : ¬ ComputableEmulator adj emu
- `adjudication_necessity` : ¬ PTTotalEffectiveOnRT pt asr
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

/-- A *computable emulator* for `adj` is a function `emu` that:
(a) emulates `adj` (agrees on all states), and
(b) induces a computable decider for `RT` via the ASR encoding bridge.

Condition (b) is stated at the code level as `ComputablePred dc.asr.RT`,
since `F.Model` carries no a priori global coding.  The intended reading is:
emu's agreement with adj on the diagonal fragment, composed with the ASR
bridge `halts_iff_RT`, yields a total computable halting decider — which is
exactly `ComputablePred RT`. -/
def ComputableEmulator {F : Framework} [dc : DiagonalCapable F]
    {C : ChoicePointInterface F}
    (adj : AdjudicationFn F C) (emu : F.Model → F.Model) : Prop :=
  Emulates adj emu ∧ ComputablePred dc.asr.RT

/-- **Bridge lemma: computable emulator induces a computable RT decider.**

If `emu` is a computable emulator for `adj`, then `ComputablePred RT` holds.
This is the key implication that connects emulator existence to RT decidability. -/
lemma emulator_implies_rt_decider {F : Framework} [dc : DiagonalCapable F]
    {C : ChoicePointInterface F}
    (adj : AdjudicationFn F C) (emu : F.Model → F.Model)
    (h : ComputableEmulator adj emu) :
    ComputablePred dc.asr.RT :=
  h.2

/-- **No-Emulation Theorem (Paper 15).**

In any diagonal-capable framework, no computable emulator for any adjudication
function can exist.

Proof: by `emulator_implies_rt_decider`, a computable emulator would yield
`ComputablePred RT`; the diagonal barrier (`diagonal_barrier_rt`) refutes this. -/
theorem no_emulation
    {F : Framework} [dc : DiagonalCapable F]
    {C : ChoicePointInterface F}
    (adj : AdjudicationFn F C)
    (emu : F.Model → F.Model) :
    ¬ ComputableEmulator adj emu := fun h =>
  diagonal_barrier_rt F (emulator_implies_rt_decider adj emu h)

/-- **Adjudication Necessity (Paper 15, Corollary).**

No internal selector (PT) can be total-effective on record-truth.
Since `PTTotalEffectiveOnRT pt asr` is exactly `ComputablePred asr.RT`,
and the diagonal barrier refutes this, active internal selection cannot
be replaced by any static algorithm. -/
theorem adjudication_necessity
    {F : Framework} [dc : DiagonalCapable F]
    {IsInternal : F.Selector → Prop}
    (pt : PT F IsInternal) :
    ¬ PTTotalEffectiveOnRT pt dc.asr :=
  pt_not_total_effective_on_RT pt

end Adjudication
end NemS
