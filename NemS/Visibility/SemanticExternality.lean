import NemS.Visibility.SelfEncoding
import NemS.Reduction.ER

/-! # NemS.Visibility.SemanticExternality -/

namespace NemS
namespace Framework

variable (F : Framework)

structure SemanticExternality where
  E      : Type
  TruthE : F.Model → E → F.Rec → Prop
  nontrivial :
    ∃ (M : F.Model) (e₁ e₂ : E) (_ : e₁ ≠ e₂) (r : F.Rec),
      (TruthE M e₁ r ∧ ¬ TruthE M e₂ r) ∨
      (¬ TruthE M e₁ r ∧ TruthE M e₂ r)

namespace SemanticExternality

variable {F : Framework}

def toExternalDep (sem : F.SemanticExternality) :
    (F.selfEncode sem.E).ExternalDependency where
  D := sem.E
  TruthD := fun ⟨M, _e_active⟩ e_param stmt =>
    match stmt with
    | Sum.inl r  => sem.TruthE M e_param r
    | Sum.inr e' => e_param = e'
  nontrivial := by
    obtain ⟨M, e₁, e₂, hne, r, h⟩ := sem.nontrivial
    refine ⟨⟨M, e₁⟩, e₁, e₂, hne, Sum.inl r, ?_⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩

/-- Semantic externality induces non-categoricity in the enlarged F⁺. -/
theorem semantic_externality_not_categorical
    (sem : F.SemanticExternality) :
    ¬ Framework.ObsCategorical
        ((F.selfEncode sem.E).enlarge (sem.toExternalDep)) :=
  (F.selfEncode sem.E).er_non_categorical sem.toExternalDep

/-- NEMS forces an internal selector for the evaluator choice. -/
theorem nems_forces_evaluator_selector
    (sem : F.SemanticExternality)
    (IsInternal : ((F.selfEncode sem.E).enlarge sem.toExternalDep).Selector → Prop)
    (hNEMS : NEMS ((F.selfEncode sem.E).enlarge sem.toExternalDep) IsInternal) :
    ∃ S : ((F.selfEncode sem.E).enlarge sem.toExternalDep).Selector,
      IsInternal S :=
  (F.selfEncode sem.E).er_nems_forces_internal_selector
    sem.toExternalDep IsInternal hNEMS

end SemanticExternality
end Framework
end NemS
