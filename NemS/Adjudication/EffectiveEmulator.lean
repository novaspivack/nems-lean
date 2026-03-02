import NemS.Adjudication.NoEmulation

/-!
# NemS.Adjudication.EffectiveEmulator

**Paper 16 (C2): Stronger No-Emulation Theorem.**

This module fulfills the deferred requirement from Paper 15: proving that any
total-effective emulator for PT on the diagonal fragment *induces* a computable
RT decider, without taking `ComputablePred RT` as a definitional hypothesis.

To do this, we formalize an `InstanceEncoding` that maps codes to physical
states (diagonal instances), and show that if an emulator is computable on these
instances, it yields a total computable halting decider.

## Key results

- `effective_emulator_induces_rt_decider` : A total-effective emulator that
  perfectly emulates the adjudicator induces a computable RT decider.
- `stronger_no_emulation` : No such effective emulator can exist, by reduction
  to the diagonal barrier.
-/

namespace NemS
namespace Adjudication

open NemS.Framework
open NemS.MFRR
open NemS.Diagonal

/-- An instance-level encoding maps a code (representing a diagonal instance)
to a physical state in the model, and provides a computable way to extract
the boolean record-truth value from the adjudicator's selection. -/
class InstanceEncoding (F : Framework) [dc : DiagonalCapable F] where
  /-- Maps a code to the corresponding physical state (diagonal instance). -/
  diagInstance : ℕ → F.Model
  /-- Extracts the boolean record-truth value from a state. -/
  extract_RT : F.Model → Bool
  /-- The adjudicator's selection on the diagonal instance correctly determines `RT n`. -/
  extract_correct : ∀ n {C : ChoicePointInterface F} (adj : AdjudicationFn F C),
    extract_RT (adj.select (diagInstance n)) = true ↔ dc.asr.RT n

/-- An emulator is *total-effective on the diagonal fragment* if its composition
with the instance encoding and RT extraction yields a computable function on codes. -/
def IsEffectiveEmulator {F : Framework} [dc : DiagonalCapable F]
    [enc : InstanceEncoding F] (emu : F.Model → F.Model) : Prop :=
  Computable (fun n => enc.extract_RT (emu (enc.diagInstance n)))

/-- Helper lemma to bridge `Computable f` to `ComputablePred p`. -/
lemma computable_pred_of_bool (p : ℕ → Prop) (f : ℕ → Bool)
    (h_comp : Computable f) (h_iff : ∀ n, f n = true ↔ p n) :
    ComputablePred p := by
  have d : DecidablePred p := fun n =>
    if h : f n = true then isTrue ((h_iff n).mp h)
    else isFalse (fun hp => h ((h_iff n).mpr hp))
  use d
  have h_eq : (fun n => @decide (p n) (d n)) = f := by
    ext n
    cases h : f n
    · have : ¬ p n := by intro hp; have := (h_iff n).mpr hp; rw [h] at this; contradiction
      have h_dec : @decide (p n) (d n) = false := by
        exact eq_false_of_ne_true (fun h_true => this (of_decide_eq_true h_true))
      exact h_dec
    · have : p n := (h_iff n).mp h
      have h_dec : @decide (p n) (d n) = true := decide_eq_true this
      exact h_dec
  rw [h_eq]
  exact h_comp

/-- **Stronger No-Emulation Lemma (Paper 16).**

Any total-effective emulator that perfectly emulates the adjudicator on the
diagonal fragment induces a computable RT decider. -/
lemma effective_emulator_induces_rt_decider
    {F : Framework} [dc : DiagonalCapable F] [enc : InstanceEncoding F]
    {C : ChoicePointInterface F}
    (adj : AdjudicationFn F C) (emu : F.Model → F.Model)
    (h_emu : Emulates adj emu)
    (h_eff : IsEffectiveEmulator emu) :
    ComputablePred dc.asr.RT := by
  apply computable_pred_of_bool dc.asr.RT (fun n => enc.extract_RT (emu (enc.diagInstance n)))
  · exact h_eff
  · intro n
    -- The emulator's output matches the adjudicator's selection
    have heq : emu (enc.diagInstance n) = adj.select (enc.diagInstance n) :=
      h_emu (enc.diagInstance n)
    rw [heq]
    -- The adjudicator's selection correctly determines RT
    exact enc.extract_correct n adj

/-- **Stronger No-Emulation Theorem (Paper 16).**

In any diagonal-capable framework with an instance encoding, no total-effective
emulator can perfectly emulate the adjudication function. -/
theorem stronger_no_emulation
    {F : Framework} [dc : DiagonalCapable F] [enc : InstanceEncoding F]
    {C : ChoicePointInterface F}
    (adj : AdjudicationFn F C) (emu : F.Model → F.Model)
    (h_emu : Emulates adj emu) :
    ¬ IsEffectiveEmulator emu := fun h_eff =>
  diagonal_barrier_rt F (effective_emulator_induces_rt_decider adj emu h_emu h_eff)

end Adjudication
end NemS
