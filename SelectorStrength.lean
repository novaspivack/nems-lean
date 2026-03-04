/-!
# SelectorStrength — Paper 29

Root barrel for the Selector Strength and Stratified Barrier Hierarchy library (Paper 29).

This library formalizes:
- **Strength** as a preorder of realizability classes (deciders/transformers)
- **Barrier schema**: under anti-decider closure + fixed-point power, no total decider
  exists for nontrivial extensional predicates
- **Bridges** to Reflection (DiagClosed ⇒ hFP) and Closure (selector at strength)
- **Instances**: trivial (all functions; barrier recovers MFP-2 under hFP from CSRI), template for computable on Nat (parametric hFP)

## Key theorem

`SelectorStrength.Theorems.BarrierSchema.no_total_decider_at_strength`
-/

import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import SelectorStrength.Theorems.BarrierSchema
import SelectorStrength.Theorems.Monotonicity
import SelectorStrength.Bridge.Reflection
import SelectorStrength.Bridge.Closure
import SelectorStrength.Instances.Trivial
import SelectorStrength.Instances.ComputableNat
