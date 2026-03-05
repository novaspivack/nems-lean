import SelectorStrength.Theorems.BarrierSchema
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.Strength
import SelectorStrength.Core.AntiDecider

/-!
# CertificationLogic.Theorems.Maximality — Paper 50 Capstone, T50.3

Maximality / boundary: any extension of the calculus that would yield a total decider
for an extensional nontrivial predicate on a diagonal-capable domain contradicts
the SelectorStrength barrier (Paper 29). Hence the calculus is complete and maximally
complete under NEMS constraints.

**Extraction lemma (informal):** If an extended calculus ⊢* could derive, for every
instance x, a certificate of T(x) vs ¬T(x) without abstention (or a protocol covering
all instances that is sound+complete for T), then there would exist a total decider
for T in the corresponding strength class. Thus maximality is the bridge from
logical/protocol completeness to computational undecidability: no such extension
can exist (boundary_maximality).
-/

set_option autoImplicit false

namespace CertificationLogic

open SelectorStrength

/-- **T50.3 Boundary (maximality schema).** Under the barrier premises (anti-decider
  closed + fixed-point premise hFP), no total decider exists for any extensional
  nontrivial predicate T. Thus the certification calculus cannot be extended to a
  universal truth logic for diagonal-capable domains without contradicting Paper 29. -/
theorem boundary_maximality
    (α : Type _)
    (T : α → Prop)
    (hExt : Extensional (· = ·) T)
    (hNontriv : Nontrivial T)
    (Sbool : Strength α Bool)
    (Sα : Strength α α)
    (hAnti : AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : α → α, Sα F → ∃ d : α, d = F d) :
    ¬ DecidableAt Sbool T :=
  no_total_decider_at_strength_nontrivial (· = ·) T hExt hNontriv Sbool Sα hAnti hFP

end CertificationLogic
