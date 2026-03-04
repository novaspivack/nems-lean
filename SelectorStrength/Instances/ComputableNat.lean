import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import SelectorStrength.Theorems.BarrierSchema
import SelectorStrength.Instances.Trivial

/-!
# SelectorStrength.Instances.ComputableNat

**Template instance for computable-on-ℕ (Paper 29).**

This is a *schema* for the barrier at "computable" strength on Nat, not yet a
fully instantiated computable theorem. We state the barrier parametrically:
given any Equiv, Sbool, Sα, AntiDeciderClosed, and a fixed-point premise hFP
for Sα, no total decider in Sbool exists for nontrivial extensional T.

The schema is reducible to supplying hFP from an actual recursion-theorem
implementation (Mathlib Partrec or SelfReference.Instances.Kleene). A fully
instantiated example—e.g. Sα(F) := Computable(F) with hFP from Nat.Partrec—
would yield a concrete theorem "¬∃ computable δ deciding T"; see Paper 29
future directions and the optional ComputableNatConcrete instantiation.
-/

set_option autoImplicit false

namespace SelectorStrength

namespace ComputableNat

variable (Equiv : Nat → Nat → Prop) (Sbool : Strength Nat Bool) (Sα : Strength Nat Nat)

/-- **Barrier for Nat at strength (Sbool, Sα)**.

When AntiDeciderClosed and the fixed-point principle hFP hold (e.g. for
computable functions, hFP from Kleene's recursion theorem or Mathlib's
Partrec), no total decider in Sbool exists for extensional nontrivial T. -/
theorem no_total_decider_nat
    (T : Nat → Prop)
    (hExt : Extensional Equiv T)
    (hNontriv : Nontrivial T)
    (hAnti : AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : Nat → Nat, Sα F → ∃ d : Nat, Equiv d (F d)) :
    ¬ DecidableAt Sbool T :=
  no_total_decider_at_strength_nontrivial Equiv T hExt hNontriv Sbool Sα hAnti hFP

/-- **Strict inclusion**: S_comp ≤ S_all (computable functions are a subset of all functions).
When Sbool and Sα are proper subsets (e.g. computable), the barrier applies at that level;
stronger levels (S_all) also have no decider when hFP holds globally. -/
theorem le_all (S : Strength Nat Bool) : S ≤ S_all :=
  fun _ _ => trivial

end ComputableNat

end SelectorStrength
