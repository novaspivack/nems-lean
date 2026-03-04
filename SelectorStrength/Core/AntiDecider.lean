import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders

/-!
# SelectorStrength.Core.AntiDecider

**Anti-decider transformer and closure (Paper 29).**

From a decider δ : α → Bool we build the transformer
  F_{δ,t₀,f₀}(x) := if δ x then f₀ else t₀.
A strength pair (Sbool for deciders, Sα for transformers) is **anti-decider closed**
when this transformer is in Sα whenever δ is in Sbool.
-/

set_option autoImplicit false

namespace SelectorStrength

universe u

variable {α : Type u}

/-- The **anti-decider transformer**: given decider δ and two values t₀, f₀,
returns t₀ when δ x = false and f₀ when δ x = true. -/
def antiDecider (δ : α → Bool) (t₀ f₀ : α) : α → α :=
  fun x => if δ x then f₀ else t₀

/-- **Anti-decider closed**: for every δ in Sbool and every t₀, f₀,
the transformer antiDecider δ t₀ f₀ is in Sα. -/
def AntiDeciderClosed (Sbool : Strength α Bool) (Sα : Strength α α) : Prop :=
  ∀ (δ : α → Bool), Sbool δ → ∀ t₀ f₀ : α, Sα (antiDecider δ t₀ f₀)

end SelectorStrength
