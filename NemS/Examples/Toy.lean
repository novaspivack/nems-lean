import NemS.Core.Trichotomy
import NemS.Reduction.ER

/-! # NemS.Examples.Toy — concrete instantiations -/

namespace NemS.Examples

open NemS

-- ============================================================
-- Example 1: Trivially categorical framework
-- ============================================================

def trivialFramework : Framework where
  Model := Unit
  Rec   := Unit
  Truth := fun _ _ => True

theorem trivialFramework_categorical : trivialFramework.ObsCategorical :=
  fun _ _ _ => Iff.rfl

-- ============================================================
-- Example 2: Bool framework — non-categorical
-- ============================================================

def boolFramework : Framework where
  Model := Bool
  Rec   := Bool
  Truth := fun M r => M = r

theorem boolFramework_not_categorical : ¬ boolFramework.ObsCategorical := by
  intro h
  have := (h true false true).mp rfl
  exact Bool.noConfusion this

-- ============================================================
-- Example 3: External dependency induces non-categoricity
-- ============================================================

def unitFramework : Framework where
  Model := Unit
  Rec   := Bool
  Truth := fun _ _ => False

def unitDep : unitFramework.ExternalDependency where
  D := Bool
  TruthD := fun _ d r => d = r
  nontrivial :=
    ⟨(), true, false, Bool.noConfusion, true,
     Or.inl ⟨rfl, fun h => Bool.noConfusion h⟩⟩

theorem unitDep_enlarged_not_categorical :
    ¬ Framework.ObsCategorical (unitFramework.enlarge unitDep) :=
  unitFramework.er_non_categorical unitDep

end NemS.Examples
