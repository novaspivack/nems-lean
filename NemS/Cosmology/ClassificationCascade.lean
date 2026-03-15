import NemS.Cosmology.FoundationalAdmissibility

/-!
# NemS.Cosmology.ClassificationCascade

**Paper 80: The Classification Cascade for Foundational Universes.**

Central module for the post-admissibility classification cascade. Collects the filter
theorems from FoundationalAdmissibility and adds the composite narrowing predicate.
Paper 80 strengthening: predicates are structure-tied (ClosureForcedProbabilityStructure,
ClosureCalibratedLawStructure), and NarrowSurvivorClass adds genuine narrowing.

The cascade sharpens admissible universes in layers:
- **SurvivorCompatible** (Phase 1): Survives closure schema (alias for ClosureCompatible)
- **ProbabilisticallyAdmissible** (Phase 2): Structure-tied GPT/Born interpretation
- **PhysicsArchitectureAdmissible** (Phase 3): Structure-tied law calibration
- **CascadeCompatible** (Composite): All three post-admissibility filters hold
- **NarrowSurvivorClass** (Narrowing): Cascade-compatible with nonvacuous worlds

The remaining horizon is near-categoricity: how small the residual class becomes
once filters are further tightened.
-/

set_option autoImplicit false

namespace NemS
namespace Cosmology

open NemS.Cosmology

/-- **Cascade compatible (Paper 80):** A foundationally viable framework that passes
all post-admissibility filters (structure-tied): probabilistic and physics-architecture
admissibility. -/
def CascadeCompatible (U : UnifiedClosureFramework) : Prop :=
  FoundationallyViable U ∧
  ProbabilisticallyAdmissible U ∧
  PhysicsArchitectureAdmissible U

/-- **Narrow survivor class (Paper 80):** U lies in the closure/Born/physics-compatible
residual class after all structure-tied filters. Adds genuine narrowing: excludes
frameworks with no worlds (Nonempty U.World). -/
def NarrowSurvivorClass (U : UnifiedClosureFramework) : Prop :=
  CascadeCompatible U ∧ Nonempty U.World

/-- **Composite filter:** SurvivorCompatible ⇒ ProbabilisticallyAdmissible ∧
PhysicsArchitectureAdmissible. Immediate from the three cascade theorems. -/
theorem probabilistic_and_physical_filter
    {U : UnifiedClosureFramework}
    (h : SurvivorCompatible U) :
    ProbabilisticallyAdmissible U ∧ PhysicsArchitectureAdmissible U :=
  ⟨survivor_compatible_implies_probabilistically_admissible h,
   foundationally_viable_implies_physics_architecture_admissible
     (survivor_compatible_implies_foundationally_viable h)⟩

/-- **Cascade compatibility theorem (Paper 80):** SurvivorCompatible ⇒ CascadeCompatible.
Structure-tied filters: closure-forced probability and closure-calibrated law. -/
theorem survivor_compatible_implies_cascade_compatible
    {U : UnifiedClosureFramework}
    (h : SurvivorCompatible U) :
    CascadeCompatible U :=
  ⟨survivor_compatible_implies_foundationally_viable h,
   survivor_compatible_implies_probabilistically_admissible h,
   foundationally_viable_implies_physics_architecture_admissible
     (survivor_compatible_implies_foundationally_viable h)⟩

/-- **Survivor filter narrows class (Paper 80):** SurvivorCompatible U implies
NarrowSurvivorClass U when U has at least one world. The cascade genuinely narrows
the survivor class: structure-tied admissibility plus nonvacuous worlds. -/
theorem survivor_filter_narrows_class
    {U : UnifiedClosureFramework}
    (h : SurvivorCompatible U)
    (hInh : Nonempty U.World) :
    NarrowSurvivorClass U :=
  ⟨survivor_compatible_implies_cascade_compatible h, hInh⟩

end Cosmology
end NemS
