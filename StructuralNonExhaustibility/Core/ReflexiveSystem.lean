import NemS.Prelude

/-!
# StructuralNonExhaustibility.Core.ReflexiveSystem

Abstract reflexive system and self-involving claims (Program V).
Schema for recovery of no-final-self-theory, no self-certifier, etc.
-/

set_option autoImplicit false

namespace StructuralNonExhaustibility

universe u v

/-- A reflexive system with self-involving claim family. -/
structure ReflexiveSystem where
  System : Type u
  Claim : Type v
  SelfInvolving : Claim → Prop
  TotalExhaustiveInternal : Prop
  BarrierHyp : Prop

/-- **No total exhaustive internalization** (schema statement).
Under barrier premises, total exhaustive internalization fails. -/
def ReflexiveSystem.NoTotalExhaustion (RS : ReflexiveSystem) : Prop :=
  RS.BarrierHyp → ¬ RS.TotalExhaustiveInternal

end StructuralNonExhaustibility
