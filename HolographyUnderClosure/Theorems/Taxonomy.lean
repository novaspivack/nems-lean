import SelectorStrength.Theorems.BarrierSchema
import SelectorStrength.Core.Deciders
import SelectorStrength.Instances.Trivial

/-!
# HolographyUnderClosure.Theorems.Taxonomy

**Paper 48 T48.4: Holography taxonomy (auditable disjunction).**

Any claimed total boundary decoder that purports to decide bulk truth must
break at least one premise: predicate not extensional/nontrivial, not internal,
not total-effective, diagonal capability absent, or PSC violated. Formally:
if all premises hold (DecidableAt + extensional + nontrivial + hFP), we get
a contradiction (the barrier).
-/

set_option autoImplicit false

namespace HolographyUnderClosure

universe u

variable {α : Type u} (Equiv : α → α → Prop)

open SelectorStrength

/-- **T48.4 Taxonomy: total decoder incompatible with barrier premises.**
If T is extensional and nontrivial and hFP holds, then DecidableAt S_all T
is false. So any "total boundary decoder" claim must relax at least one of:
extensionality, nontriviality, internality/total-effectiveness, diagonal
capability, or PSC. -/
theorem taxonomy_total_decoder_incompatible
    (T : α → Prop)
    (hExt : Extensional Equiv T)
    (hNontriv : Nontrivial T)
    (hFP : ∀ F : α → α, ∃ d : α, Equiv d (F d)) :
    ¬ DecidableAt (S_all (α := α)) T :=
  no_total_decider_all Equiv T hExt hNontriv hFP

end HolographyUnderClosure
