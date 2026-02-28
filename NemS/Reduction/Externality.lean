import NemS.Core.Basics

/-!
# NemS.Reduction.Externality

An `ExternalDependency` packages a parameter space `D` and a dependent
truth-valuation `TruthD : Model → D → Rec → Prop` such that varying `d`
within `D` can change record-truth for some model and record statement.

This is the abstract formalization of "vacuum choice," "measure choice,"
"observer map," etc. — any extra datum whose variation affects record-level
predictions.

Harmless conventions (gauge choices, coordinate systems) that do NOT affect
record-truth are excluded by the nontriviality condition.
-/


namespace NemS

namespace Framework

variable (F : Framework)

/-- An `ExternalDependency` for framework `F` is:
- a parameter space `D`,
- a dependent truth-valuation `TruthD` that extends `F.Truth` with a
  dependency on `d : D`, and
- a nontriviality witness showing that some `d₁ ≠ d₂` genuinely change
  the truth-value of some record statement for some model. -/
structure ExternalDependency where
  /-- The parameter space (vacua, branches, measures, observer maps, …). -/
  D      : Type
  /-- Truth valuation dependent on the external parameter. -/
  TruthD : F.Model → D → F.Rec → Prop
  /-- Nontriviality: varying `d` changes record-truth for some (M, r). -/
  nontrivial :
    ∃ (M : F.Model) (d₁ d₂ : D) (_ : d₁ ≠ d₂) (r : F.Rec),
      (TruthD M d₁ r ∧ ¬ TruthD M d₂ r) ∨
      (¬ TruthD M d₁ r ∧ TruthD M d₂ r)

namespace ExternalDependency

variable {F : Framework}

/-- Extract the witnessing models and parameter values from nontriviality. -/
theorem get_witness (dep : F.ExternalDependency) :
    ∃ (M : F.Model) (d₁ d₂ : dep.D) (_ : d₁ ≠ d₂) (r : F.Rec),
      ¬ (dep.TruthD M d₁ r ↔ dep.TruthD M d₂ r) := by
  obtain ⟨M, d₁, d₂, hne, r, h⟩ := dep.nontrivial
  exact ⟨M, d₁, d₂, hne, r, by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact fun h => h2 (h.mp h1)
    · exact fun h => h1 (h.mpr h2)⟩

end ExternalDependency

end Framework

end NemS
