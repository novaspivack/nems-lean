import RecordEntropy.Core.EntropyFinite
import ArrowOfTime.Core.RecordFiltration
import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import SelectorStrength.Theorems.BarrierSchema

set_option autoImplicit false

/-!
# RecordEntropy.Theorems.NoncomputabilityBarrier

**Paper 42: Fixed-instance entropy claim (schema).**

This module provides the fixed-instance predicate T(n) := (H(t) = n) for fixed
Filt and t. For a single instance, T is trivially decidable, so the barrier does
not bite here. The **uniform** barrier (codes over encoded filtrations/times)
lives in RecordEntropy.Theorems.UniformEntropyBarrier.
-/

namespace RecordEntropy

universe u v

open ArrowOfTime
open ArrowOfTime.RecordFiltration

variable {World : Type u} {Obs : Type v} (Filt : RecordFiltration World Obs) (t : ArrowOfTime.Time)
variable [Fintype (Filt.WorldTypeAt t)]

/-- **Record-entropy claim predicate:** T(n) := (recordEntropy Filt t = n). -/
def entropyClaim (n : Nat) : Prop :=
  recordEntropy Filt t = n

/-- The entropy claim is extensional for Nat equality. -/
theorem entropyClaim_extensional : SelectorStrength.Extensional (· = ·) (entropyClaim Filt t) := by
  intro x y heq
  rw [heq]

/-- The entropy claim is nontrivial: T(recordEntropy Filt t) holds, T(recordEntropy Filt t + 1) does not. -/
theorem entropyClaim_nontrivial : SelectorStrength.Nontrivial (entropyClaim Filt t) := by
  refine ⟨⟨recordEntropy Filt t, rfl⟩, ⟨recordEntropy Filt t + 1, Ne.symm (Nat.succ_ne_self (recordEntropy Filt t))⟩⟩

/-- **Barrier for record entropy (Nat-encoded):** Under AntiDeciderClosed and hFP at strength S,
no total decider in Sbool exists for the predicate "H(t) = n". -/
theorem no_total_decider_entropy
    (Sbool : SelectorStrength.Strength Nat Bool) (Sα : SelectorStrength.Strength Nat Nat)
    (hAnti : SelectorStrength.AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : Nat → Nat, Sα F → ∃ d : Nat, (· = ·) d (F d)) :
    ¬ SelectorStrength.DecidableAt Sbool (entropyClaim Filt t) :=
  SelectorStrength.no_total_decider_at_strength_nontrivial (· = ·) (entropyClaim Filt t)
    (entropyClaim_extensional Filt t) (entropyClaim_nontrivial Filt t) Sbool Sα hAnti hFP

end RecordEntropy
