import NemS.Cosmology.UnifiedClosureFramework
import GPTClosure.Examples.Toy
import GPTClosure.Core.EffectsStates

/-!
# NemS.Cosmology.Bridges.ToGPTClosure

**Bridge: Post-67 Phase 2 — Probabilistic admissibility (GPT/Born-rule compatibility).**

Links the unified closure framework to GPT closure (Paper 39). A UCF is probabilistically
admissible when it is survivor-compatible and GPT closure structure exists (effects span
the state space in some classical simplex instance).

**Paper 80 strengthening:** `UCFHasObsEqRespectingGPTInterpretation U` is U-relative:
there exists ι : U.World → State (ToySpace 1) that respects ObsEqAt at stage 0. Combined
with SurvivorCompatible in FoundationalAdmissibility yields ClosureForcedProbabilityStructure.
-/

set_option autoImplicit false

namespace NemS
namespace Cosmology
namespace Bridges

open NemS.Cosmology
open GPTClosure.Examples.Toy
open OrderedUnitSpace

/-- **GPT closure structure exists:** Some classical simplex has effects spanning the space.
Used to formally link ProbabilisticallyAdmissible to GPTClosure (Paper 39). -/
def GPTClosureStructureExists : Prop :=
  ∃ (n : ℕ) (_ : NeZero n), (ToySpace n).effectSpan = ⊤

/-- GPT closure structure exists: the classical simplex (ToySpace 1) has effectSpan = ⊤. -/
theorem gpt_closure_structure_exists : GPTClosureStructureExists := by
  refine ⟨1, inferInstance, ?_⟩
  exact toy_effect_span_top 1

/-- **UCF has ObsEq-respecting GPT interpretation (Paper 80):** U-relative. There exists
ι : U.World → State (ToySpace 1) that respects ObsEqAt at stage 0: observationally
equivalent worlds map to the same GPT state. -/
def UCFHasObsEqRespectingGPTInterpretation (U : UnifiedClosureFramework) : Prop :=
  ∃ (ι : U.World → State (ToySpace 1)),
    (ToySpace 1).effectSpan = ⊤ ∧
    ∀ w₁ w₂ : U.World,
      (U.toRecordFiltration).ObsEqAt 0 w₁ w₂ → ι w₁ = ι w₂

/-- Every UCF admits an ObsEq-respecting interpretation into ToySpace 1.
The constant map (all worlds → unique state) is ObsEqAt-respecting. -/
theorem ucf_has_obsEq_respecting_gpt_interpretation (U : UnifiedClosureFramework) :
    UCFHasObsEqRespectingGPTInterpretation U :=
  ⟨fun _ => classicalState 1 (fun _ => 1) (by simp) (fun _ => by norm_num),
   toy_effect_span_top 1, fun _ _ _ => rfl⟩

end Bridges
end Cosmology
end NemS
