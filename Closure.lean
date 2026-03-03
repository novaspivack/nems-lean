/-!
# Closure — Theory Closure and Audit Toolkit

Root barrel file for the Closure library.

This library provides a physics-agnostic API for *theories about systems*:
observational semantics, world-types, selectors (sections of the quotient),
and a parameterized notion of internality.  It supports the **audit soundness**
theorem: any decider for a non-invariant predicate implies a selector.
The **A0 bridge** (Closure.Bridge.SelfReferenceInstance) shows that when
a theory has internal representability (repr with repr_spec), it yields
an `SRI'` instance so that SelfReference's MFP-1 and diagonal barrier apply.

## Module structure

- `Closure.Core`      — ObsSemantics, Selector, Internal, Canonicalization, Effective.
- `Closure.Theorems`  — AuditSoundness, Preservation, BoundedSelector (nailed computable instance).
- `Closure.Bridge`   — SelfReferenceInstance (theory with repr ⇒ SRI').
- `Closure.Examples` — FintypeWorld (toy nailed instance: finite worlds ⇒ selector).
-/

import Closure.Core.ObsSemantics
import Closure.Core.Selector
import Closure.Core.Internal
import Closure.Core.Canonicalization
import Closure.Core.Effective
import Closure.Theorems.AuditSoundness
import Closure.Theorems.Preservation
import Closure.Theorems.BoundedSelector
import Closure.Bridge.SelfReferenceInstance
import Closure.Examples.FintypeWorld
