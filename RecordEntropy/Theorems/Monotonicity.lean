import RecordEntropy.Core.EntropyFinite
import ArrowOfTime.Core.RecordFiltration
import ArrowOfTime.Core.Refinement
import ArrowOfTime.Theorems.ArrowRefinement
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

/-!
# RecordEntropy.Theorems.Monotonicity

**Paper 42: Record entropy is monotone under record growth; strict when refinement is strict.**

The forgetful map from WorldTypeAt (t+1) to WorldTypeAt t is surjective, so
card(WorldTypeAt (t+1)) ≥ card(WorldTypeAt t). When StrictGrowthAt t, forget
is not injective, so the inequality is strict.
-/

namespace RecordEntropy

universe u v

open ArrowOfTime
open ArrowOfTime.RecordFiltration

variable {World : Type u} {Obs : Type v} (Filt : RecordFiltration World Obs) (t : ArrowOfTime.Time)

section Monotonicity

variable [Fintype (Filt.WorldTypeAt t)] [Fintype (Filt.WorldTypeAt (t + 1))]

/-- The forgetful map at t is surjective: every t-class is the image of some (t+1)-class. -/
theorem forget_surjective : Function.Surjective (Filt.forget t) := by
  intro x
  refine Quotient.inductionOn x (fun w => ?_)
  use Filt.toWorldTypeAt (t + 1) w
  exact Filt.forget_coherent t w

/-- **Record entropy is monotone:** H(t+1) ≥ H(t). -/
theorem recordEntropy_monotone :
    recordEntropy Filt (t + 1) ≥ recordEntropy Filt t := by
  exact Fintype.card_le_of_surjective (Filt.forget t) (forget_surjective Filt t)

end Monotonicity

section Strict

variable [Fintype (Filt.WorldTypeAt t)] [Fintype (Filt.WorldTypeAt (t + 1))]

/-- When card(α) = card(β) and f : α → β is surjective, f is injective (finite pigeonhole). -/
theorem injective_of_surjective_of_card_eq (α β : Type*) [Fintype α] [Fintype β] (f : α → β)
    (hcard : Fintype.card α = Fintype.card β) (hsurj : Function.Surjective f) :
    Function.Injective f :=
  Function.Surjective.injective_of_finite (Fintype.equivOfCardEq hcard) hsurj

/-- **Strict monotonicity when refinement is strict:** if StrictGrowthAt t then H(t+1) > H(t). -/
theorem recordEntropy_strict (hStrict : Filt.StrictGrowthAt t) :
    recordEntropy Filt (t + 1) > recordEntropy Filt t := by
  have hle := recordEntropy_monotone Filt t
  apply Nat.lt_iff_le_and_ne.mpr
  constructor
  · exact hle
  · intro heq
    obtain ⟨a, b, hne, heq'⟩ := Filt.strict_refinement t hStrict
    have hcard : Fintype.card (Filt.WorldTypeAt (t + 1)) = Fintype.card (Filt.WorldTypeAt t) :=
      by rw [← recordEntropy, ← recordEntropy, heq]
    have hinj : Function.Injective (Filt.forget t) :=
      injective_of_surjective_of_card_eq _ _ (Filt.forget t) hcard (forget_surjective Filt t)
    exact hne (hinj heq')

end Strict

end RecordEntropy
