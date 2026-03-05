import CausalNonlocality.Theorems.NoGo
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.Strength
import SelectorStrength.Core.AntiDecider

/-!
# CausalNonlocality.Examples.ToyNoGo

**Paper 46: Barrier witness (parametric in hFP).**

We use Nat as the domain (diagonal-capable when hFP is supplied by Reflection or
Partrec elsewhere). Predicate ToyT = "= 0" (extensional, nontrivial). The theorem
is **parametric in hFP**: under any Sbool, Sα, AntiDeciderClosed, and fixed-point
premise hFP for Nat, no total decider for ToyT exists. No axiom: hFP is a
theorem parameter; concrete witnesses supply it from Reflection (Paper 28) or
Partrec (e.g. Papers 30, 42, 44).
-/

set_option autoImplicit false

namespace CausalNonlocality

open SelectorStrength

/-- Predicate on Nat (stand-in for "world-type in given class" on encoded local-view maps). -/
def ToyT (n : Nat) : Prop := n = 0

theorem toyT_extensional : Extensional (α := Nat) (· = ·) ToyT :=
  fun {_ _} h => ⟨fun hx => h.symm.trans hx, fun hy => h.trans hy⟩

theorem toyT_nontrivial : Nontrivial (α := Nat) ToyT :=
  ⟨⟨0, rfl⟩, ⟨1, Nat.succ_ne_zero 0⟩⟩

/-- **Barrier witness (parametric).** For any strength (Sbool, Sα) that is
anti-decider closed and has the fixed-point premise hFP on Nat, no total decider
for ToyT exists. When hFP is supplied by Reflection or Partrec (no axiom),
this yields a concrete no-go for local semantic determinacy. -/
theorem toy_no_go
    (Sbool : Strength Nat Bool)
    (Sα : Strength Nat Nat)
    (hAnti : AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : Nat → Nat, Sα F → ∃ d : Nat, d = F d) :
    ¬ DecidableAt Sbool ToyT :=
  no_total_decider_at_strength_nontrivial (· = ·) ToyT toyT_extensional toyT_nontrivial
    Sbool Sα hAnti hFP

end CausalNonlocality
