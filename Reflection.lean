/-!
# Reflection — Reflection as a Resource

Root barrel file for the Reflection library (Paper 28).

This library provides a **resource theory of reflection**: stratified
representability, fixed points under restricted internalization, and
a selector-strength hierarchy. It sits between:

- **Closure** (Paper 27): audit calculus, internality, no free bits
- **SelfReference** (Paper 26): full repr-spec → MFP-1, diagonal barrier

Reflection adds the graded middle ground: **how much internalization
is enough** for which fixed points, and how that maps to selector
strength (IIa/IIb) in an abstract way.

## Headline theorem: Diagonal Closure

If R is closed under the diagonalization template
`F ↦ (c ↦ F(quote(run c c)))`, then every F ∈ R has a mixed fixed point.

## Module structure

- `Reflection.Core`     — SRI_R (restricted repr), DiagClosed
- `Reflection.Theorems` — restricted_master_fixed_point (Diagonal Closure Theorem)
- `Reflection.Hierarchy` — separation examples, recovery of full MFP-1
- `Reflection.Bridge`  — conceptual bridge from Closure internality to R-classes
-/

import Reflection.Core.SRI_R
import Reflection.Theorems.DiagonalClosure
import Reflection.Hierarchy.Examples
import Reflection.Hierarchy.Separation
import Reflection.Bridge.ClosureInstance
