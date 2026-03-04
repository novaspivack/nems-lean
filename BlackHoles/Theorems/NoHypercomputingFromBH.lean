import NemS.Prelude
import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import SelectorStrength.Theorems.BarrierSchema

/-!
# BlackHoles.Theorems.NoHypercomputingFromBH

**Paper 37: No hypercomputing from black holes.**

A total-effective "decoder" (deciding a nontrivial extensional predicate on
the decoding-outcome space) would contradict the SelectorStrength barrier
(Paper 29/35). So under diagonal capability, no total-effective decoder
exists — black holes do not supply an internal oracle.
-/

set_option autoImplicit false

namespace BlackHoles

universe u

variable {α : Type u}

/-- **No hypercomputing from black holes (abstract form)**.
Under the same premises as the no-internal-hypercomputer theorem (Paper 35),
no total decider exists at strength Sbool for any nontrivial extensional
predicate T on the outcome space α. So any "black hole decoder" that
total-effectively decides such a predicate is ruled out. -/
theorem no_hypercomputing_from_bh
    (T : α → Prop)
    (hExt : SelectorStrength.Extensional (· = ·) T)
    (hNontriv : SelectorStrength.Nontrivial T)
    (Sbool : SelectorStrength.Strength α Bool)
    (Sα : SelectorStrength.Strength α α)
    (hAnti : SelectorStrength.AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : α → α, Sα F → ∃ d : α, d = F d) :
    ¬ SelectorStrength.DecidableAt Sbool T :=
  SelectorStrength.no_total_decider_at_strength_nontrivial (· = ·) T hExt hNontriv Sbool Sα hAnti hFP

end BlackHoles
