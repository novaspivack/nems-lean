import NemS.Core.Categoricity
import NemS.Core.Selectors

/-! # NemS.Core.Trichotomy — the flagship theorem -/

namespace NemS
namespace Framework

variable {F : Framework}
variable {IsInternal : F.Selector → Prop}

/-- Branch 3: the framework requires external model selection. -/
def NeedsExternalSelection (F : Framework) (IsInternal : F.Selector → Prop) : Prop :=
  ¬ F.ObsCategorical ∧ ¬ ∃ S : F.Selector, IsInternal S

/-- NEMS: the negation of branch 3. -/
def NEMS (F : Framework) (IsInternal : F.Selector → Prop) : Prop :=
  ¬ NeedsExternalSelection F IsInternal

/-- NEMS ↔ categorical ∨ internal selector exists. -/
theorem nems_iff_cat_or_internal :
    NEMS F IsInternal ↔
    F.ObsCategorical ∨ ∃ S : F.Selector, IsInternal S := by
  unfold NEMS NeedsExternalSelection
  push_neg
  constructor
  · intro h
    by_cases hcat : F.ObsCategorical
    · exact Or.inl hcat
    · exact Or.inr (h hcat)
  · intro h hNC
    rcases h with hcat | hsel
    · exact absurd hcat hNC
    · exact hsel

/-- **NEMS Trichotomy** -/
theorem nems_trichotomy (F : Framework) (IsInternal : F.Selector → Prop) :
    F.ObsCategorical ∨
    (∃ S : F.Selector, IsInternal S) ∨
    NeedsExternalSelection F IsInternal := by
  by_cases hcat : F.ObsCategorical
  · exact Or.inl hcat
  · by_cases hsel : ∃ S : F.Selector, IsInternal S
    · exact Or.inr (Or.inl hsel)
    · exact Or.inr (Or.inr ⟨hcat, hsel⟩)

/-- Under NEMS: categorical or internal selector. -/
theorem nems_implies_cat_or_internal
    (h : NEMS F IsInternal) :
    F.ObsCategorical ∨ ∃ S : F.Selector, IsInternal S :=
  nems_iff_cat_or_internal.mp h

/-- NEMS + non-categorical ⇒ internal selector. -/
theorem nems_noncat_implies_internal
    (hNEMS : NEMS F IsInternal)
    (hNC : ¬ F.ObsCategorical) :
    ∃ S : F.Selector, IsInternal S := by
  rcases nems_implies_cat_or_internal hNEMS with hcat | hsel
  · exact absurd hcat hNC
  · exact hsel

/-- NEMS + no internal selector ⇒ categorical. -/
theorem nems_no_selector_implies_cat
    (hNEMS : NEMS F IsInternal)
    (hNoSel : ¬ ∃ S : F.Selector, IsInternal S) :
    F.ObsCategorical := by
  rcases nems_implies_cat_or_internal hNEMS with hcat | hsel
  · exact hcat
  · exact absurd hsel hNoSel

end Framework
end NemS
