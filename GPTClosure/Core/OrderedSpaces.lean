-- Ordered unit space: finite-dimensional real vector space with cone and order unit
-- Used as the base for GPT effects and states (Paper 39)
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Cone.Basic

variable (V : Type*) [AddCommGroup V] [Module ℝ V]

/-- Cone predicate on V: closed under addition, nonnegative scaling, and 0 ∈ cone.
    We also assume pointed: if x and -x are in cone then x = 0. -/
structure ConePredicate (V : Type*) [AddCommGroup V] [Module ℝ V] where
  Pos : V → Prop
  pos_zero : Pos 0
  pos_add : ∀ x y, Pos x → Pos y → Pos (x + y)
  pos_smul : ∀ (c : ℝ) (x : V), 0 ≤ c → Pos x → Pos (c • x)
  pos_neg_iff_zero : ∀ x, Pos x → Pos (-x) → x = 0

namespace ConePredicate

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (K : ConePredicate V)

def le (a b : V) : Prop := K.Pos (b - a)

theorem le_refl (a : V) : K.le a a := by
  rw [ConePredicate.le, sub_self]; exact K.pos_zero

theorem le_trans (a b c : V) : K.le a b → K.le b c → K.le a c := by
  intro hab hbc; rw [ConePredicate.le] at *
  have : c - a = (c - b) + (b - a) := by abel
  rw [this]; exact K.pos_add _ _ hbc hab

theorem le_antisymm (a b : V) : K.le a b → K.le b a → a = b := by
  intro hab hba; rw [ConePredicate.le] at hab hba
  have heq : b - a = -(a - b) := by abel
  rw [heq] at hab
  exact sub_eq_zero.mp (K.pos_neg_iff_zero (a - b) hba hab)

end ConePredicate

/-- Ordered unit space: V with a cone predicate and an order unit u. -/
structure OrderedUnitSpace (V : Type*) [AddCommGroup V] [Module ℝ V] where
  cone : ConePredicate V
  orderUnit : V
  pos_order_unit : cone.Pos orderUnit

namespace OrderedUnitSpace

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (S : OrderedUnitSpace V)

def le (a b : V) : Prop := S.cone.le a b

theorem le_refl (a : V) : S.le a a := S.cone.le_refl a
theorem le_trans (a b c : V) : S.le a b → S.le b c → S.le a c := S.cone.le_trans a b c
theorem le_antisymm (a b : V) : S.le a b → S.le b a → a = b := S.cone.le_antisymm a b

instance instPartialOrder : PartialOrder V where
  le := S.le
  le_refl := S.le_refl
  le_trans := S.le_trans
  le_antisymm := S.le_antisymm

/-- LE V from any OrderedUnitSpace (so downstream modules can use ≤). -/
instance orderedUnitSpaceLE (S' : OrderedUnitSpace V) : LE V where
  le := S'.cone.le

end OrderedUnitSpace
