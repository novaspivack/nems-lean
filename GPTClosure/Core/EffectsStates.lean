-- Effects and states for GPT (Paper 39)
import GPTClosure.Core.OrderedSpaces
import Mathlib.LinearAlgebra.LinearMap.Basic

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (S : OrderedUnitSpace V)

namespace OrderedUnitSpace

/-- Effect: element e with 0 ≤ e ≤ u. -/
def Effect := { e : V // 0 ≤ e ∧ e ≤ S.orderUnit }

instance : Coe (S.Effect) V := ⟨Subtype.val⟩

def orderUnitEffect : S.Effect := ⟨S.orderUnit, S.le_refl _, le_refl S.orderUnit⟩

/-- State: positive linear functional ω with ω(u) = 1. -/
structure State where
  toFun : V →ₗ[ℝ] ℝ
  nonneg' : ∀ x, S.cone.Pos x → 0 ≤ toFun x
  norm_one : toFun S.orderUnit = 1

namespace State

instance : FunLike S.State V (fun _ => ℝ) where
  coe ω := ω.toFun
  coe_injective' _ _ h := by cases _; cases _; congr; exact LinearMap.coe_injective h

@[simp] theorem coe_apply (ω : S.State) (x : V) : ω x = ω.toFun x := rfl

theorem nonneg (ω : S.State) (x : V) (h : S.cone.Pos x) : 0 ≤ ω x := ω.nonneg' x h

theorem norm_one (ω : S.State) : ω S.orderUnit = 1 := ω.norm_one

/-- Probability of effect e in state ω: Pr_ω(e) = ω(e). -/
def prob (ω : S.State) (e : S.Effect) : ℝ := ω (e : V)

theorem prob_nonneg (ω : S.State) (e : S.Effect) : 0 ≤ ω.prob e := by
  unfold State.prob; apply ω.nonneg; rw [OrderedUnitSpace.le, sub_zero]
  exact e.2.1

theorem prob_le_one (ω : S.State) (e : S.Effect) : ω.prob e ≤ 1 := by
  unfold State.prob
  have pos : S.cone.Pos (S.orderUnit - (e : V)) := e.2.2
  have := ω.nonneg (S.orderUnit - (e : V)) pos
  rw [LinearMap.map_sub, ω.norm_one] at this
  linarith

theorem prob_bounds (ω : S.State) (e : S.Effect) : 0 ≤ ω.prob e ∧ ω.prob e ≤ 1 :=
  ⟨ω.prob_nonneg e, ω.prob_le_one e⟩

end State

end OrderedUnitSpace
