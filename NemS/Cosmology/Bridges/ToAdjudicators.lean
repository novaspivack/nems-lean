import NemS.Cosmology.UnifiedClosureFramework
import NemS.Cosmology.StrongCosmologicalClosureSchema
import NemS.Cosmology.Bridges.ToSemanticFloor
import NemS.Cosmology.Bridges.ToArrowOfTime
import NemS.Cosmology.Bridges.ToFinality
import NemS.Observers.AdjudicatorNetwork
import NemS.Observers.RecordStability

/-!
# NemS.Cosmology.Bridges.ToAdjudicators

**Extension B: Bridge to adjudicator infrastructure (Paper 17).**

Under StrongCosmologicalClosureSchema (base schema + GRS + NCC), and given
the Paper 17 witness clause, the framework admits an adjudicator network.
-/

set_option autoImplicit false

namespace NemS
namespace Cosmology
namespace Bridges

open NemS.Cosmology
open NemS.Observers

/-- **Theorem: Strong closure schema ⇒ adjudicator infrastructure.**

Under the strong schema (with global record stability and nonlocal coherence),
and given the witness that those constraints entail a network, an adjudicator
network exists. Invokes Paper 17's necessary_adjudicators theorem.
-/
theorem strong_closure_schema_implies_adjudicator_infrastructure
    {U : UnifiedClosureFramework}
    (h : StrongCosmologicalClosureSchema U)
    (h_witness : (GlobalRecordStability U.toFramework ∧ NonlocalCoherenceConstraints U.toFramework) →
      AdjudicatorNetwork U.toFramework) :
    AdjudicatorNetwork U.toFramework :=
  necessary_adjudicators ⟨h.psc⟩ h.global_record_stability h.nonlocal_coherence h_witness

/-- **Cosmological closure unification with adjudicators.**

The minimal summit theorem (admissible ∧ irreversible ∧ no external selection)
plus adjudicator network existence, under the strong schema and witness.
-/
theorem cosmological_closure_unification_with_adjudicators
    {U : UnifiedClosureFramework}
    (h : StrongCosmologicalClosureSchema U)
    (h_witness : (GlobalRecordStability U.toFramework ∧ NonlocalCoherenceConstraints U.toFramework) →
      AdjudicatorNetwork U.toFramework) :
    ClosureAdmissibleInitiality U ∧
    StructuralIrreversibility U ∧
    ClosureRealizedHistory U ∧
    AdjudicatorNetwork U.toFramework := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact closure_schema_implies_admissible_initiality h.toCosmologicalClosureSchema
  · exact closure_schema_implies_structural_irreversibility h.toCosmologicalClosureSchema
  · exact closure_schema_implies_internal_realized_history h.toCosmologicalClosureSchema
  · exact strong_closure_schema_implies_adjudicator_infrastructure h h_witness

end Bridges
end Cosmology
end NemS
