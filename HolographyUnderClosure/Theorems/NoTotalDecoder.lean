import SelectorStrength.Theorems.BarrierSchema
import SelectorStrength.Core.Deciders
import SelectorStrength.Instances.Trivial

/-!
# HolographyUnderClosure.Theorems.NoTotalDecoder

**Paper 48 T48.3: No total-effective boundary decoder.**

A "boundary decoder" that total-effectively computes bulk world-type (or decides
a nontrivial extensional predicate thereon) would be a total decider at diagonal-capable
strength. The Paper 29 barrier forbids such a decider. So holography does not
imply an internal total-effective reconstruction.
-/

set_option autoImplicit false

namespace HolographyUnderClosure

universe u

variable {α : Type u} (Equiv : α → α → Prop)

open SelectorStrength

/-- **No total-effective boundary decoder (schema).** Under the barrier assumptions,
no total decider exists for an extensional nontrivial predicate T on the type α
(e.g. boundary codes or boundary world-types encoding bulk truth). -/
theorem no_total_effective_boundary_decoder
    (T : α → Prop)
    (hExt : Extensional Equiv T)
    (hNontriv : Nontrivial T)
    (hFP : ∀ F : α → α, ∃ d : α, Equiv d (F d)) :
    ¬ DecidableAt (S_all (α := α)) T :=
  no_total_decider_all Equiv T hExt hNontriv hFP

end HolographyUnderClosure
