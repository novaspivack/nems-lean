import FTLConstraints.Theorems.NoCompiler
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.Strength
import SelectorStrength.Core.AntiDecider

/-!
# FTLConstraints.Examples.ToyEPR

**Paper 47: Toy witness (parametric in hFP).**

Minimal two-site style setup: correlation type = Nat (codes for correlation data),
predicate ToyT = "= 0" (extensional, nontrivial). A "compiler" would be a total
decider for ToyT. The theorem is **parametric in hFP**: under any Sbool, Sα,
AntiDeciderClosed, and fixed-point premise hFP on Nat, no such decider exists.
Concrete hFP from Reflection or Partrec yields 0 axioms.
-/

set_option autoImplicit false

namespace FTLConstraints

open SelectorStrength

/-- Toy predicate (stand-in for "world-type in given class" on correlation codes). -/
def ToyT (n : Nat) : Prop := n = 0

theorem toyT_extensional : Extensional (α := Nat) (· = ·) ToyT :=
  fun {_ _} h => ⟨fun hx => h.symm.trans hx, fun hy => h.trans hy⟩

theorem toyT_nontrivial : Nontrivial (α := Nat) ToyT :=
  ⟨⟨0, rfl⟩, ⟨1, Nat.succ_ne_zero 0⟩⟩

/-- **No-compiler witness (parametric).** For any strength (Sbool, Sα) that is
anti-decider closed and has the fixed-point premise hFP on Nat, no total decider
for ToyT exists — hence no spooky-to-signal compiler. Supply hFP from Reflection
or Partrec for a concrete result with 0 axioms. -/
theorem toy_no_spooky_to_signal_compiler
    (Sbool : Strength Nat Bool)
    (Sα : Strength Nat Nat)
    (hAnti : AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : Nat → Nat, Sα F → ∃ d : Nat, d = F d) :
    ¬ DecidableAt Sbool ToyT :=
  no_total_decider_at_strength_nontrivial (· = ·) ToyT toyT_extensional toyT_nontrivial
    Sbool Sα hAnti hFP

end FTLConstraints
