import NemS.Prelude

/-!
# NemS.Core.Basics

The fundamental abstract structure for the NEMS framework:
a `Framework` bundles a type of models/realizations, a type of record
statements, and a truth-valuation relating them.

This is intentionally minimal: no specific logic, no dynamics, no physics.
The theorems in the rest of the library are parametric over any `Framework`.
-/


namespace NemS

universe u v

/-- A `Framework` is the abstract setting for NEMS reasoning.
- `Model` : the type of admissible realizations / histories / worlds.
- `Rec`   : the type of record statements (propositions about stable records).
- `Truth` : the truth-valuation; `Truth M r` means record statement `r`
             holds in realization `M`. -/
structure Framework where
  Model : Type u
  Rec   : Type v
  Truth : Model → Rec → Prop

namespace Framework

variable (F : Framework)

/-- Convenient notation for truth in a framework. -/
def holds (M : F.Model) (r : F.Rec) : Prop := F.Truth M r

end Framework

end NemS
