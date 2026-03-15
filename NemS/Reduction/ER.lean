import NemS.Reduction.EnlargedSpace
import NemS.Core.Trichotomy

/-! # NemS.Reduction.ER — Externality Reduction -/

namespace NemS
namespace Framework

variable (F : Framework)

/-- ER: a nontrivial external dependency induces non-categoricity. -/
theorem er_non_categorical
    (dep : F.ExternalDependency) :
    ¬ Framework.ObsCategorical (F.enlarge dep) :=
  F.enlarged_not_categorical dep

/-- NEMS on enlarged space forces an internal selector. -/
theorem er_nems_forces_internal_selector
    (dep : F.ExternalDependency)
    (IsInternal : (F.enlarge dep).Selector → Prop)
    (hNEMS : NEMS (F.enlarge dep) IsInternal) :
    ∃ S : (F.enlarge dep).Selector, IsInternal S := by
  rcases nems_implies_cat_or_internal hNEMS with hcat | hsel
  · exact absurd hcat (er_non_categorical F dep)
  · exact hsel

/-- Determinacy-PSC: every external dependency has an internal selector. -/
def DeterminacyPSC : Prop :=
  ∀ (dep : F.ExternalDependency)
    (IsInternal : (F.enlarge dep).Selector → Prop),
    NEMS (F.enlarge dep) IsInternal →
    ∃ S : (F.enlarge dep).Selector, IsInternal S

/-- NEMS + ER ⇒ determinacy-PSC. -/
theorem nems_er_implies_detpsc
    (_h : ∀ (dep : F.ExternalDependency)
           (IsInternal : (F.enlarge dep).Selector → Prop),
           NEMS (F.enlarge dep) IsInternal) :
    F.DeterminacyPSC :=
  fun dep IsInternal hNEMS => er_nems_forces_internal_selector F dep IsInternal hNEMS

/-- DeterminacyPSC holds for every framework: whenever NEMS holds on an enlarged space,
an internal selector exists. -/
theorem determinacyPSC_of_framework (F : Framework) : F.DeterminacyPSC :=
  fun dep IsInternal hNEMS => er_nems_forces_internal_selector F dep IsInternal hNEMS

end Framework
end NemS
