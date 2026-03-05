import HolographyUnderClosure.Theorems.NoTotalDecoder
import SelectorStrength.Theorems.BarrierSchema
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.Strength
import SelectorStrength.Core.AntiDecider

/-!
# HolographyUnderClosure.Examples.Toy

**Paper 48: Barrier witness (parametric in hFP).**

Boundary data encoded as Nat (codes); predicate ToyT = "= 0" (extensional,
nontrivial). A total-effective "boundary decoder" for this predicate would be
a total decider for ToyT. The theorem is **parametric in hFP**: under any
Sbool, Sα, AntiDeciderClosed, and fixed-point premise on Nat, no such decider
exists. Instantiate hFP from Reflection or Partrec for 0 axioms. The full
Fin 4 bulk/boundary toy (surjective world-type map) is described in the paper.
-/

set_option autoImplicit false

namespace HolographyUnderClosure

open SelectorStrength

/-- Toy bulk predicate on boundary codes (stand-in for "bulk world-type in given class"). -/
def ToyT (n : Nat) : Prop := n = 0

theorem toyT_extensional : Extensional (α := Nat) (· = ·) ToyT :=
  fun {_ _} h => ⟨fun hx => h.symm.trans hx, fun hy => h.trans hy⟩

theorem toyT_nontrivial : Nontrivial (α := Nat) ToyT :=
  ⟨⟨0, rfl⟩, ⟨1, Nat.succ_ne_zero 0⟩⟩

/-- **No total boundary decoder (toy witness).** For any strength (Sbool, Sα)
that is anti-decider closed and has the fixed-point premise hFP on Nat,
no total decider for ToyT exists—hence no total-effective boundary decoder
for this predicate. Supply hFP from Reflection or Partrec for 0 axioms. -/
theorem toy_no_total_boundary_decoder
    (Sbool : Strength Nat Bool)
    (Sα : Strength Nat Nat)
    (hAnti : AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : Nat → Nat, Sα F → ∃ d : Nat, d = F d) :
    ¬ DecidableAt Sbool ToyT :=
  no_total_decider_at_strength_nontrivial (· = ·) ToyT toyT_extensional toyT_nontrivial
    Sbool Sα hAnti hFP

end HolographyUnderClosure
