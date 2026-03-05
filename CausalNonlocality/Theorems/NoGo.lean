import SelectorStrength.Theorems.BarrierSchema
import SelectorStrength.Core.Deciders
import SelectorStrength.Instances.Trivial

/-!
# CausalNonlocality.Theorems.NoGo

**Paper 46: No-go for local semantic determinacy.**

Under factorization (Paper 45), world-type is determined by the restriction map
(local views). "Local semantic determinacy" would mean a total-effective procedure
computes world-type from that map. We show this is impossible under the
selector-strength barrier (Paper 29): such a procedure would be a total decider
for an extensional nontrivial predicate on a diagonal-capable type.

**Theorem schema:** For any type α of local-view maps with equivalence Equiv,
any predicate T that is extensional and nontrivial (e.g. "world-type in class τ")
cannot have a total decider in a strength class that is diagonal-capable (anti-decider
closed + fixed-point premise). Hence local semantic determinacy fails.
-/

set_option autoImplicit false

namespace CausalNonlocality

universe u

variable {α : Type u} (Equiv : α → α → Prop)

open SelectorStrength

/-- **No-go (abstract schema).** Under the barrier assumptions (anti-decider closed +
fixed-point premise), no total decider exists for any extensional nontrivial predicate T.
This is the barrier applied to the type α (e.g. local-view maps). -/
theorem no_local_semantic_determinacy
    (T : α → Prop)
    (hExt : Extensional Equiv T)
    (hNontriv : Nontrivial T)
    (hFP : ∀ F : α → α, ∃ d : α, Equiv d (F d)) :
    ¬ DecidableAt (S_all (α := α)) T :=
  no_total_decider_all Equiv T hExt hNontriv hFP

/-- **Locality reading:** same as `no_local_semantic_determinacy`; underscores that the
barrier is interpreted as effective failure of locality gluing/determinacy (Paper 46). -/
theorem no_total_effective_local_semantic_determinacy
    (T : α → Prop)
    (hExt : Extensional Equiv T)
    (hNontriv : Nontrivial T)
    (hFP : ∀ F : α → α, ∃ d : α, Equiv d (F d)) :
    ¬ DecidableAt (S_all (α := α)) T :=
  no_local_semantic_determinacy Equiv T hExt hNontriv hFP

end CausalNonlocality
