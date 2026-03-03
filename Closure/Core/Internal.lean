import Closure.Core.Selector

/-!
# Closure.Core.Internal

Parameterized **internality** predicate: "X is definable / realizable
within the theory."  We do not bake in computability or a specific
logic; downstream modules (e.g. definability-in-a-theory, computability)
instantiate this typeclass.

This is the heart of the audit story: a selector is "internal" iff it
is realizable within the theory; outsourcing corresponds to selection
that is not internal.
-/

set_option autoImplicit false

namespace Closure

universe u v

/-- A typeclass for **internality**: a predicate "Internal : α → Prop"
meaning "x is definable / realizable within the theory."

Downstream modules provide instances, e.g.:
- definability in a base logic
- computability (partial/total)
- provably total in a base theory T
-/
class InternalPred (α : Type u) where
  /-- `Internal x` means `x` is realizable within the theory. -/
  Internal : α → Prop

/-- A selector for semantics `S` is internal if the underlying section
function is internal (in the sense of the chosen `InternalPred` instance
for `S.WorldType → World`). -/
def SelectorInternal {World : Type u} {Obs : Type v} (S : ObsSemantics World Obs)
    [InternalPred (S.WorldType → World)] (sel : Selector S) : Prop :=
  InternalPred.Internal sel.sel

/-- No-free-bits principle (formal criterion): if there is more than
one world-type, then any claim that depends on a choice of representative
is not observationally forced.  We state the structural fact: when
`NeedsSelection` holds, the theory has a nontrivial choice point. -/
theorem needsSelection_iff_not_subsingleton (World Obs : Type u) (S : ObsSemantics World Obs) :
    S.NeedsSelection ↔ ¬ Subsingleton S.WorldType :=
  Iff.rfl

end Closure
