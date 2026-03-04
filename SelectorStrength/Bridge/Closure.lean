import Closure.Core.ObsSemantics
import Closure.Core.Selector
import SelectorStrength.Core.Strength

/-!
# SelectorStrength.Bridge.Closure

**Selector at strength S (Paper 29 + Paper 27).**

A selector for observational semantics S is **at strength S_sel** when the
section function is in the class S_sel. Monotonicity: stronger S_sel ⇒
more selectors. This ties selector existence to the strength poset.
-/

set_option autoImplicit false

namespace SelectorStrength

universe u v

variable {World : Type u} {Obs : Type v} (S : Closure.ObsSemantics World Obs)

/-- **Selector at strength S_sel**: there exists a selector whose section function
is in the class S_sel (e.g. internal, computable). -/
def SelectorAt (S_sel : (S.WorldType → World) → Prop) : Prop :=
  ∃ sel : Closure.Selector S, S_sel sel.sel

/-- If S_sel1 ≤ S_sel2 (pointwise), then SelectorAt S_sel1 S → SelectorAt S_sel2 S. -/
theorem selectorAt_mono (S_sel1 S_sel2 : (S.WorldType → World) → Prop)
    (hle : ∀ f, S_sel1 f → S_sel2 f) :
    SelectorAt S S_sel1 → SelectorAt S S_sel2 := by
  intro ⟨sel, h1⟩
  exact ⟨sel, hle sel.sel h1⟩

end SelectorStrength
