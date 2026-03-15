import NemS.Cosmology.UnifiedClosureFramework
import NemS.Cosmology.CosmologicalClosureSchema
import NemS.Cosmology.CosmologicalClosureUnification
import NemS.Cosmology.Bridges.ToSemanticFloor
import NemS.Cosmology.Bridges.ToArrowOfTime
import NemS.Cosmology.Bridges.ToFinality
import NemS.Cosmology.Bridges.ToGPTClosure
import NemS.Cosmology.Bridges.ToLawCalibration
import NemS.Reduction.ER

/-!
# NemS.Cosmology.FoundationalAdmissibility

**EPIC_67_FA: Foundational Admissibility classification.**

Defines when a unified closure framework is foundationally viable and closure-compatible.
Proves: ¬ClosureCompatible ⇒ viability failure (contrapositive of schema ⇒ viable).
-/

set_option autoImplicit false

open Classical

namespace NemS
namespace Cosmology

open NemS.Cosmology
open NemS.Cosmology.Bridges
open NemS.Framework

/-- **Foundationally viable:** A framework satisfies all three grand-unification components:
admissible initiality (semantic floor), structural irreversibility, internal realized history. -/
def FoundationallyViable (U : UnifiedClosureFramework) : Prop :=
  ClosureAdmissibleInitiality U ∧
  StructuralIrreversibility U ∧
  ClosureRealizedHistory U

/-- **Closure compatible:** The framework satisfies the cosmological closure schema
(Diagonal + Universe + PSC). -/
def ClosureCompatible (U : UnifiedClosureFramework) : Prop :=
  Nonempty (CosmologicalClosureSchema U)

/-- **Foundational Admissibility Theorem (EPIC_67_FA).**

Closure compatibility implies foundational viability.
Proof: from cosmological_closure_unification. -/
theorem foundational_admissibility
    {U : UnifiedClosureFramework}
    (h : ClosureCompatible U) :
    FoundationallyViable U := by
  obtain ⟨hc⟩ := h
  exact cosmological_closure_unification hc

/-- **Converse (EPIC_67_FA):** FoundationallyViable ⇒ ClosureCompatible.

Foundational viability implies closure compatibility. Constructs the schema from the
three viable components: admissible initiality supplies diagonal + universe; internal
realized history supplies NEMS; DeterminacyPSC holds for every framework. -/
theorem foundationally_viable_implies_closure_compatible
    {U : UnifiedClosureFramework}
    (h : FoundationallyViable U) :
    ClosureCompatible U := by
  obtain ⟨h_initial, _h_irrev, h_history⟩ := h
  obtain ⟨h_dc, h_u⟩ := h_initial
  have hun : Nonempty (Universe U.toFramework) := by obtain ⟨u, _⟩ := h_u; exact ⟨u⟩
  refine ⟨{
    diagonal := Classical.choice h_dc
    has_universe := hun
    psc := {
      nems := h_history
      detPSC := determinacyPSC_of_framework U.toFramework
    }
  }⟩

/-- **Viability failure (contrapositive):** ¬FoundationallyViable ⇒ ¬ClosureCompatible.

If a framework is not foundationally viable, it cannot satisfy the closure schema.
Equivalent formulation: viability failure implies incompatibility with closure. -/
theorem viability_failure_implies_not_closure_compatible
    {U : UnifiedClosureFramework}
    (h : ¬ FoundationallyViable U) :
    ¬ ClosureCompatible U :=
  fun hc => h (foundational_admissibility hc)

/-!
## Post-67 classification cascade (scaffolding)

| Phase | Predicate | Status |
|-------|-----------|--------|
| 0 | FoundationallyViable | ✓ Defined |
| 1 | SurvivorCompatible | ✓ Alias for ClosureCompatible (survives schema) |
| 2 | ProbabilisticallyAdmissible | ✓ Bridge to GPTClosure (Paper 39) |
| 3 | PhysicsArchitectureAdmissible | ✓ Bridge to LawCalibration (Paper 44) |
| 4 | Categoricity | NemS.Core.Categoricity — existing |
-/

/-- **Survivor compatible (Post-67 Phase 1):** Survives closure refinement.
Alias: frameworks satisfying the closure schema survive (no internal contradiction). -/
def SurvivorCompatible (U : UnifiedClosureFramework) : Prop :=
  ClosureCompatible U

/-- SurvivorCompatible ⇒ FoundationallyViable (from foundational_admissibility). -/
theorem survivor_compatible_implies_foundationally_viable
    {U : UnifiedClosureFramework}
    (h : SurvivorCompatible U) :
    FoundationallyViable U :=
  foundational_admissibility h

/-- **Closure-forced probability structure (Paper 80):** U-relative. Survivor-compatible U
admits an interpretation from U.World to GPT state space that respects ObsEqAt at stage 0. -/
def ClosureForcedProbabilityStructure (U : UnifiedClosureFramework) : Prop :=
  SurvivorCompatible U ∧ Bridges.UCFHasObsEqRespectingGPTInterpretation U

/-- SurvivorCompatible ⇒ ClosureForcedProbabilityStructure (ToGPTClosure bridge). -/
theorem survivor_compatible_implies_closure_forced_probability_structure
    {U : UnifiedClosureFramework}
    (h : SurvivorCompatible U) :
    ClosureForcedProbabilityStructure U :=
  ⟨h, Bridges.ucf_has_obsEq_respecting_gpt_interpretation U⟩

/-- **Probabilistically admissible (Post-67 Phase 2, Paper 80 strong):** Survivor-compatible
and U admits closure-forced probability structure (structure-tied). -/
def ProbabilisticallyAdmissible (U : UnifiedClosureFramework) : Prop :=
  SurvivorCompatible U ∧ ClosureForcedProbabilityStructure U

/-- SurvivorCompatible ⇒ ProbabilisticallyAdmissible (structure-tied). -/
theorem survivor_compatible_implies_probabilistically_admissible
    {U : UnifiedClosureFramework}
    (h : SurvivorCompatible U) :
    ProbabilisticallyAdmissible U :=
  ⟨h, survivor_compatible_implies_closure_forced_probability_structure h⟩

/-- **Closure-calibrated law structure (Paper 80):** U-relative. Foundationally viable U
admits a choice from U.InitState to Law with all images fixed points. -/
def ClosureCalibratedLawStructure (U : UnifiedClosureFramework) : Prop :=
  FoundationallyViable U ∧
  ∃ (choice : U.InitState → LawCalibration.Law),
    ∀ i : U.InitState, LawCalibration.IsFixedPoint (choice i)

/-- FoundationallyViable ⇒ ClosureCalibratedLawStructure (InitState → Law.minimal). -/
theorem foundationally_viable_implies_closure_calibrated_law_structure
    {U : UnifiedClosureFramework}
    (h : FoundationallyViable U) :
    ClosureCalibratedLawStructure U :=
  ⟨h, ⟨fun _ => LawCalibration.Law.minimal, fun _ => LawCalibration.all_fixed LawCalibration.Law.minimal⟩⟩

/-- **Physics-architecture admissible (Post-67 Phase 3, Paper 80 strong):** Foundationally
viable and U has closure-calibrated law structure (structure-tied). -/
def PhysicsArchitectureAdmissible (U : UnifiedClosureFramework) : Prop :=
  FoundationallyViable U ∧ ClosureCalibratedLawStructure U

/-- FoundationallyViable ⇒ PhysicsArchitectureAdmissible (structure-tied). -/
theorem foundationally_viable_implies_physics_architecture_admissible
    {U : UnifiedClosureFramework}
    (h : FoundationallyViable U) :
    PhysicsArchitectureAdmissible U :=
  ⟨h, foundationally_viable_implies_closure_calibrated_law_structure h⟩

end Cosmology
end NemS
