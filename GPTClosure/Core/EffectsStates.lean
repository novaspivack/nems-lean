-- Effects and states for GPT (Paper 39)
import GPTClosure.Core.OrderedSpaces
import Mathlib.Algebra.Module.LinearMap.Basic

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (OUS : OrderedUnitSpace V)

namespace OrderedUnitSpace

/-- Effect: element e with 0 ≤ e ≤ u. -/
def Effect (S : OrderedUnitSpace V) :=
  { e : V // @LE.le V (OrderedUnitSpace.orderedUnitSpaceLE S) 0 e ∧
            @LE.le V (OrderedUnitSpace.orderedUnitSpaceLE S) e S.orderUnit }

def orderUnitEffect : OUS.Effect := ⟨OUS.orderUnit, by show OUS.cone.Pos (OUS.orderUnit - 0); rw [sub_zero]; exact OUS.pos_order_unit, OUS.le_refl OUS.orderUnit⟩

/-- State: positive linear functional ω with ω(u) = 1. -/
structure State (S : OrderedUnitSpace V) where
  toFun : V →ₗ[ℝ] ℝ
  nonneg' : ∀ x, S.cone.Pos x → 0 ≤ toFun x
  norm_one : toFun S.orderUnit = 1

@[ext] theorem State.ext (S' : OrderedUnitSpace V) (ω₁ ω₂ : S'.State) (h : ω₁.toFun = ω₂.toFun) : ω₁ = ω₂ := by
  cases ω₁ with | mk _ _ _ => cases ω₂ with | mk _ _ _ => congr 1

namespace StateExt

@[simp] theorem toFun_apply (ω : OUS.State) (x : V) : ω.toFun x = ω.toFun x := rfl

theorem nonneg (ω : OUS.State) (x : V) (h : OUS.cone.Pos x) : 0 ≤ ω.toFun x := ω.nonneg' x h

theorem apply_orderUnit (ω : OUS.State) : ω.toFun OUS.orderUnit = 1 := ω.norm_one

end StateExt

/-- Probability of effect e in state ω: Pr_ω(e) = ω(e). -/
def stateEffectProb (ω : OUS.State) (e : OUS.Effect) : ℝ := ω.toFun e.val

theorem prob_nonneg (ω : OUS.State) (e : OUS.Effect) : 0 ≤ ω.toFun e.val := by
  have he : OUS.cone.Pos e.val := by rw [← sub_zero e.val]; exact e.2.1
  exact ω.nonneg' e.val he

theorem prob_le_one (ω : OUS.State) (e : OUS.Effect) : ω.toFun e.val ≤ 1 := by
  have pos : OUS.cone.Pos (OUS.orderUnit - e.val) := e.2.2
  have := ω.nonneg' (OUS.orderUnit - e.val) pos
  rw [LinearMap.map_sub, ω.norm_one] at this
  linarith

theorem prob_bounds (ω : OUS.State) (e : OUS.Effect) : 0 ≤ ω.toFun e.val ∧ ω.toFun e.val ≤ 1 := by
  constructor
  · have he : OUS.cone.Pos e.val := by rw [← sub_zero e.val]; exact e.2.1
    exact ω.nonneg' e.val he
  · have pos : OUS.cone.Pos (OUS.orderUnit - e.val) := e.2.2
    have := ω.nonneg' (OUS.orderUnit - e.val) pos
    rw [LinearMap.map_sub, ω.norm_one] at this
    linarith

namespace State
/-- Dot notation: ω.prob e -/
def prob (ω : OUS.State) (e : OUS.Effect) : ℝ := ω.toFun e.val
end State

end OrderedUnitSpace
