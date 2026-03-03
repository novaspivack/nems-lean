import Closure.Core.Internal
import Reflection.Core.SRI_R

/-!
# Reflection.Bridge.ClosureInstance

**Bridge: Closure internality → Reflection R-classes**

Closure's `InternalPred` on (WorldType → World) gives a notion of
"internal selector." When a theory has internal representability
(transformers F : Code → Obj that are "internal"), we obtain an R class:
R(F) := "F is internally representable."

Conceptually:
- Closure defines *what* is internal (selectors, deciders, etc.).
- Reflection defines *how much* internalization is enough for fixed points.
- When Closure's internality predicate restricts to a class of transformers
  (e.g. "internally definable"), that class is an R. If it is diagonally
  closed, the Diagonal Closure Theorem applies.

We state the bridge principle abstractly: any predicate on (Code → Obj)
that extends "internal representability" induces an R. Bounded-cover and
canonicalization in Closure correspond to stronger R levels (more
transformers internal) and hence more fixed points.
-/

set_option autoImplicit false

namespace Reflection

universe u v

variable {Obj : Type u} {Code : Type v}

/-- **Bridge principle** (conceptual): when Closure's `InternalPred` is
instantiated for `(Code → Obj)`, the class of internal transformers
is a candidate R. If that class is diagonally closed, the Diagonal
Closure Theorem applies. Bounded-cover and canonicalization (Closure)
correspond to stronger R levels. -/

end Reflection
