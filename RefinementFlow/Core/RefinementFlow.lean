import ArrowOfTime.Core.RecordFiltration
import ArrowOfTime.Core.Refinement

set_option autoImplicit false

/-!
# RefinementFlow.Core.RefinementFlow

**Paper 41: Refinement Flow of World-Types.**

Re-exports and extends ArrowOfTime: record filtration, stage world-types,
and the forgetful maps. This module defines iterated forget (forgetFromTo)
and its coherence (naturality).
-/

namespace RefinementFlow

universe u v

variable {World : Type u} {Obs : Type v}

open ArrowOfTime
open ArrowOfTime.RecordFiltration

/-- The forgetful map from stage t' down to stage t (when t ≤ t').
Induced by iterating the single-step forget. -/
def forgetFromTo (Filt : ArrowOfTime.RecordFiltration World Obs) (t : Time) (t' : Time) (h : t ≤ t') :
    Filt.WorldTypeAt t' → Filt.WorldTypeAt t :=
  match t' with
  | 0 => by
      have : t = 0 := Nat.eq_zero_of_le_zero h
      subst this
      exact id
  | m + 1 => by
      by_cases hle : t ≤ m
      · exact forgetFromTo Filt t m hle ∘ Filt.forget m
      · have heq : t = m + 1 := (Nat.le_succ_iff.mp h).resolve_left hle
        subst heq
        exact id
termination_by t'

/-- Coherence: forgetFromTo t t' sends the quotient of w to the quotient of w at stage t. -/
theorem forgetFromTo_coherent (Filt : ArrowOfTime.RecordFiltration World Obs) (t t' : Time) (h : t ≤ t') (w : World) :
    forgetFromTo Filt t t' h (Filt.toWorldTypeAt t' w) = Filt.toWorldTypeAt t w := by
  induction t' with
  | zero =>
    have : t = 0 := Nat.eq_zero_of_le_zero h
    subst this
    simp only [forgetFromTo]
    rfl
  | succ m ih =>
    by_cases hle : t ≤ m
    · simp only [forgetFromTo, hle]
      split_ifs
      · rw [Function.comp_apply, Filt.forget_coherent m w]
        exact ih hle
      · trivial
    · have heq : t = m + 1 := (Nat.le_succ_iff.mp h).resolve_left hle
      subst heq
      simp only [forgetFromTo, hle, Nat.succ_eq_add_one]
      rfl

/-- One-step case: forgetFromTo from t+1 down to t equals the single-step forget (Paper 36). -/
theorem forgetFromTo_succ (Filt : ArrowOfTime.RecordFiltration World Obs) (t : Time) :
    forgetFromTo Filt t (t + 1) (Nat.le_succ t) = Filt.forget t := by
  ext x
  refine Quotient.inductionOn x (fun w => ?_)
  have key : (Quotient.mk (Filt.obsEqAtSetoid (t + 1)) w : Filt.WorldTypeAt (t + 1)) = Filt.toWorldTypeAt (t + 1) w := rfl
  rw [key]
  rw [forgetFromTo_coherent, Filt.forget_coherent]

/-- Naturality: composing forgetFromTo t' t'' with forgetFromTo t t' gives forgetFromTo t t''. -/
theorem forgetFromTo_naturality (Filt : ArrowOfTime.RecordFiltration World Obs) (t t' t'' : Time) (ht : t ≤ t') (ht' : t' ≤ t'')
    (x : Filt.WorldTypeAt t'') :
    forgetFromTo Filt t t' ht (forgetFromTo Filt t' t'' ht' x) = forgetFromTo Filt t t'' (Nat.le_trans ht ht') x := by
  refine Quotient.inductionOn x (fun w => ?_)
  have key'' : (Quotient.mk (Filt.obsEqAtSetoid t'') w : Filt.WorldTypeAt t'') = Filt.toWorldTypeAt t'' w := rfl
  rw [key'']
  rw [forgetFromTo_coherent, forgetFromTo_coherent, forgetFromTo_coherent]

end RefinementFlow
