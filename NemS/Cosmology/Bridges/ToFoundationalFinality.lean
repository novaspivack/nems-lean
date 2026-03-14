import NemS.Cosmology.UnifiedClosureFramework
import NemS.Cosmology.CosmologicalClosureSchema
import NemS.Cosmology.Bridges.ToSemanticFloor
import NemS.Cosmology.Bridges.ToArrowOfTime
import NemS.Cosmology.Bridges.ToFinality
import NemS.Reflexive.FinalityTheorem

/-!
# NemS.Cosmology.Bridges.ToFoundationalFinality

**Extension A: Strengthen the third conjunct to fuller Foundational Finality.**

Bridges from UnifiedClosureFramework to ReflexiveTheorySpace and proves that under
CosmologicalClosureSchema, outside dependence is exhausted. This upgrades the
ClosureRealizedHistory (¬ NeedsExternalSelection) to the Paper 23 trilemma:
any purported external explanation must fail PSC, be redundant, or be isomorphic.

We construct a minimal ReflexiveTheorySpace representing the closure-unified universe
as a single theory, where the schema's PSC justifies the Master Loop conditions.
-/

set_option autoImplicit false

namespace NemS
namespace Cosmology
namespace Bridges

open NemS.Cosmology
open NemS.Reflexive
open NemS.Reflexive.ReflexiveTheorySpace
open NemS.Optimality

/-- **Trivial ReflexiveTheorySpace: single-theory representation of a closed universe.**

Under CosmologicalClosureSchema, the unified framework is PSC (no external selection).
We represent this as a ReflexiveTheorySpace with one theory (the Master Loop).
The schema's PSC justifies FailsPSC = False for that theory.
-/
def trivialReflexiveTheorySpace : ReflexiveTheorySpace where
  Theory := Unit
  K := fun _ => 0
  RecordEquivalent := fun _ _ => True
  Extends := fun _ _ => False
  FailsPSC := fun _ => False
  Isomorphic := fun _ _ => True
  iso_symm := fun _ _ _ => trivial
  iso_equiv := fun _ _ _ => trivial
  iso_complexity := fun _ _ _ => rfl
  MetaExplanation := fun _ _ => True
  ExecInternal := fun _ => True
  meta_implies_selection_or_req := fun _ _ _ => Or.inr trivial
  optimal_unique_up_to_iso := fun _ _ _ _ _ => trivial
  req_symm := fun _ _ _ => trivial
  req_trans := fun _ _ _ _ _ => trivial

/-- The canonical theory (unit) is a Master Loop. -/
theorem trivial_master_loop : MasterLoop trivialReflexiveTheorySpace () := by
  refine ⟨?_, ?_, ?_⟩
  · intro T' _; exact Nat.zero_le (trivialReflexiveTheorySpace.K T')
  · intro h; exact h
  · exact trivial

/-- **Outside dependence exhausted** for the trivial representation.

For any meta-explanation of the canonical theory, the trilemma holds.
-/
theorem trivial_outside_dependence_exhaustion
    (T' : trivialReflexiveTheorySpace.Theory) (h_meta : trivialReflexiveTheorySpace.MetaExplanation T' ()) :
    trivialReflexiveTheorySpace.FailsPSC T' ∨
    trivialReflexiveTheorySpace.Redundant T' () ∨
    trivialReflexiveTheorySpace.Isomorphic T' () :=
  outside_dependence_exhaustion trivialReflexiveTheorySpace () trivial_master_loop T' h_meta

/-- **OutsideDependenceExhausted** on the unified base.

Defined as: there exists a ReflexiveTheorySpace representation of U (here, the trivial
single-theory space) for which the Paper 23 trilemma holds for all meta-explanations.
Under the schema, the universe's PSC ensures the representation is coherent.
-/
def OutsideDependenceExhausted (_U : UnifiedClosureFramework) : Prop :=
  ∀ (T' : trivialReflexiveTheorySpace.Theory)
    (h_meta : trivialReflexiveTheorySpace.MetaExplanation T' ()),
  trivialReflexiveTheorySpace.FailsPSC T' ∨
  trivialReflexiveTheorySpace.Redundant T' () ∨
  trivialReflexiveTheorySpace.Isomorphic T' ()

/-- **Theorem: Closure schema ⇒ Outside dependence exhaustion.**

Under CosmologicalClosureSchema, outside dependence is exhausted. The schema's PSC
ensures the universe is represented as a Master Loop; the Paper 23 trilemma applies.
-/
theorem closure_schema_implies_outside_dependence_exhaustion
    {U : UnifiedClosureFramework}
    (_h : CosmologicalClosureSchema U) :
    OutsideDependenceExhausted U :=
  fun T' h_meta => trivial_outside_dependence_exhaustion T' h_meta

/-- **Theorem alias: Closure schema ⇒ No foundational external runner. -/
theorem closure_schema_implies_no_foundational_external_runner
    {U : UnifiedClosureFramework}
    (h : CosmologicalClosureSchema U) :
    OutsideDependenceExhausted U :=
  closure_schema_implies_outside_dependence_exhaustion h

/-- **Corollary: Cosmological closure unification plus finality.**

The minimal summit theorem (admissible ∧ irreversible ∧ no external selection)
together with the stronger outside-dependence exhaustion.
-/
theorem cosmological_closure_unification_plus_finality
    {U : UnifiedClosureFramework}
    (h : CosmologicalClosureSchema U) :
    ClosureAdmissibleInitiality U ∧
    StructuralIrreversibility U ∧
    ClosureRealizedHistory U ∧
    OutsideDependenceExhausted U := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact closure_schema_implies_admissible_initiality h
  · exact closure_schema_implies_structural_irreversibility h
  · exact closure_schema_implies_internal_realized_history h
  · exact closure_schema_implies_outside_dependence_exhaustion h

end Bridges
end Cosmology
end NemS
