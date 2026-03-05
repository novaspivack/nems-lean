import CertificationLogic.Theorems.Maximality
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.Strength
import SelectorStrength.Core.AntiDecider

/-!
# CertificationLogic.Examples.ToyBoundary — Paper 50 Capstone

Boundary toy on Nat: predicate ToyT n := (n = 0). Parametric in hFP; under barrier
premises (anti-decider closed + hFP), no total decider exists (SelectorStrength barrier).
Shows why the calculus cannot be extended to universal truth for diagonal-capable domains.
-/

set_option autoImplicit false

namespace CertificationLogic.Examples

open SelectorStrength

/-- Predicate on Nat (diagonal-capable when hFP is supplied from Reflection/Partrec). -/
def ToyT (n : Nat) : Prop := n = 0

theorem toyT_extensional : Extensional (α := Nat) (· = ·) ToyT :=
  fun {_ _} h => ⟨fun hx => h.symm.trans hx, fun hy => h.trans hy⟩

theorem toyT_nontrivial : Nontrivial (α := Nat) ToyT :=
  ⟨⟨0, rfl⟩, ⟨1, Nat.succ_ne_zero 0⟩⟩

/-- **Boundary witness (parametric in hFP).** Under any Sbool, Sα, AntiDeciderClosed,
  and fixed-point premise hFP on Nat, no total decider for ToyT exists.
  Instantiate hFP from Reflection (Paper 28) or Partrec elsewhere; no axiom. -/
theorem toy_boundary
    (Sbool : Strength Nat Bool)
    (Sα : Strength Nat Nat)
    (hAnti : AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : Nat → Nat, Sα F → ∃ d : Nat, d = F d) :
    ¬ DecidableAt Sbool ToyT :=
  CertificationLogic.boundary_maximality Nat ToyT toyT_extensional toyT_nontrivial
    Sbool Sα hAnti hFP

end CertificationLogic.Examples
