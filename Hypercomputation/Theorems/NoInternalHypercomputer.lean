import SelectorStrength.Theorems.BarrierSchema
import SelectorStrength.Instances.Trivial
import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import Hypercomputation.Core.HypercomputerClaim

/-!
# Hypercomputation.Theorems.NoInternalHypercomputer

**No internal total hypercomputer (Paper 35 flagship).**

Under anti-decider closure and the fixed-point principle, no total internal
hypercomputer exists for any extensional nontrivial predicate. This is a
direct wrapper over the Paper 29 barrier schema.
-/

set_option autoImplicit false

namespace Hypercomputation

open SelectorStrength

universe u

variable {α : Type u}
variable (Equiv : α → α → Prop)
variable (Sbool : Strength α Bool) (Sα : Strength α α)

/-- **No internal hypercomputer at strength (Paper 35).**

Under `AntiDeciderClosed` and the fixed-point principle `hFP`, no total decider
exists at strength `Sbool` for any extensional nontrivial predicate T.

This is the flagship theorem of Paper 35: any purported internal total
hypercomputer for such a T would contradict the barrier. -/
theorem no_internal_hypercomputer_at_strength (T : α → Prop)
    (hExt : Extensional Equiv T)
    (hNon : Nontrivial T)
    (hAnti : AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : α → α, Sα F → ∃ d : α, Equiv d (F d)) :
    ¬ HasInternalHypercomputerAt Sbool T :=
  SelectorStrength.no_total_decider_at_strength_nontrivial Equiv T hExt hNon
    Sbool Sα hAnti hFP

/-- **No total internal hypercomputer.** Alias with Paper 35 naming. -/
theorem no_total_internal_hypercomputer (T : α → Prop)
    (hExt : Extensional Equiv T)
    (hNon : Nontrivial T)
    (hAnti : AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : α → α, Sα F → ∃ d : α, Equiv d (F d)) :
    ¬ HasInternalHypercomputerAt Sbool T :=
  no_internal_hypercomputer_at_strength Equiv Sbool Sα T hExt hNon hAnti hFP

/-- **Corollary: no total hypercomputer at trivial (all-functions) strength.**

When the strength is "all functions" (S_all) and the equivalence has a
global fixed-point property, no total hypercomputer exists. Recovers the
raw logical barrier (MFP-2). -/
theorem no_total_hypercomputer_all (T : α → Prop)
    (hExt : Extensional Equiv T)
    (hNon : Nontrivial T)
    (hFP : ∀ F : α → α, ∃ d : α, Equiv d (F d)) :
    ¬ HasInternalHypercomputerAt (S_all (α := α)) T := by
  have hAnti := antiDeciderClosed_all (α := α)
  exact no_internal_hypercomputer_at_strength Equiv
    (S_all (α := α)) (S_all_α (α := α))
    T hExt hNon hAnti (fun F _ => hFP F)

end Hypercomputation
