import StructuralNonExhaustibility.Core.ReflexiveSystem

/-!
# StructuralNonExhaustibility.Theorems.NoTotalExhaustion

Schema: BarrierHyp ⇒ ¬ TotalExhaustiveInternal.
Concrete recovery in Bridges/ToSemanticSelfDescription.
-/

set_option autoImplicit false

namespace StructuralNonExhaustibility

open ReflexiveSystem

/-- **Schema theorem.** When NoTotalExhaustion holds as a proved implication,
we obtain the conclusion. (Instance-specific proofs live in Bridges.) -/
theorem no_total_exhaustion_of (RS : ReflexiveSystem)
    (h : RS.NoTotalExhaustion) (hBarrier : RS.BarrierHyp) :
    ¬ RS.TotalExhaustiveInternal :=
  h hBarrier

end StructuralNonExhaustibility
