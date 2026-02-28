import NemS.Reduction.Externality
import NemS.Core.Categoricity

/-!
# NemS.Reduction.EnlargedSpace

Given a framework `F` and an external dependency `dep`, we construct the
*enlarged framework* `F'` whose models are pairs `(M, d) : F.Model × dep.D`.

The record statements and truth-valuation of `F'` are:
- `Rec'  := F.Rec`
- `Truth' (M, d) r := dep.TruthD M d r`

This is the constructive core of Externality Reduction (ER): any external
dependency is literally "model multiplicity in the enlarged space."
-/

namespace NemS

namespace Framework

variable (F : Framework)

/-- Construct the enlarged framework from an external dependency. -/
def enlarge (dep : F.ExternalDependency) : Framework where
  Model := F.Model × dep.D
  Rec   := F.Rec
  Truth := fun ⟨M, d⟩ r => dep.TruthD M d r

/-- The two witnesses from nontriviality are *not* observationally equivalent
in the enlarged space. -/
theorem enlarge_nontrivial_not_obsEq (dep : F.ExternalDependency) :
    ∃ p q : (F.enlarge dep).Model, ¬ Framework.ObsEq (F.enlarge dep) p q := by
  obtain ⟨M, d₁, d₂, _hne, r, hne_iff⟩ := dep.get_witness
  exact ⟨⟨M, d₁⟩, ⟨M, d₂⟩, fun h => hne_iff (h r)⟩

/-- The enlarged framework is **not** observationally categorical. -/
theorem enlarged_not_categorical (dep : F.ExternalDependency) :
    ¬ Framework.ObsCategorical (F.enlarge dep) := by
  obtain ⟨p, q, hne⟩ := F.enlarge_nontrivial_not_obsEq dep
  intro hcat
  exact hne (hcat p q)

end Framework

end NemS
