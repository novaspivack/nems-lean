import SelectorStrength.Core.Strength

/-!
# SelectorStrength.Core.Deciders

**Deciders and extensional predicates (Paper 29).**

- TotalDecider T δ: δ is a Boolean decider for predicate T.
- DecidableAt S T: T has a decider in strength class S.
- Extensional: T respects an equivalence Equiv.
- Nontrivial: T has both a true and a false instance.
-/

set_option autoImplicit false

namespace SelectorStrength

universe u

variable {α : Type u}

/-- A predicate `T : α → Prop` is **extensional** for `Equiv` if it respects the equivalence. -/
def Extensional (Equiv : α → α → Prop) (T : α → Prop) : Prop :=
  ∀ {x y}, Equiv x y → (T x ↔ T y)

/-- **Total decider**: δ : α → Bool decides T when δ x = true ↔ T x for all x. -/
def TotalDecider (T : α → Prop) (δ : α → Bool) : Prop :=
  ∀ x, δ x = true ↔ T x

/-- **Decidable at strength S**: T has some total decider in class S. -/
def DecidableAt (S : Strength α Bool) (T : α → Prop) : Prop :=
  ∃ δ : α → Bool, S δ ∧ TotalDecider T δ

/-- **Nontrivial** predicate: has at least one true and one false instance. -/
def Nontrivial (T : α → Prop) : Prop :=
  (∃ x, T x) ∧ (∃ x, ¬ T x)

end SelectorStrength
