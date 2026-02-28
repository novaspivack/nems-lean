import NemS.Core.Trichotomy
import NemS.Reduction.ER

/-! # NemS.Meta.AuditProtocol -/

namespace NemS
namespace Framework

variable (F : Framework) (IsInternal : F.Selector → Prop)

/-- A framework passes the NEMS audit iff it is categorical or has an internal selector. -/
def PassAudit : Prop :=
  F.ObsCategorical ∨ ∃ S : F.Selector, IsInternal S

theorem passAudit_iff_nems :
    PassAudit F IsInternal ↔ NEMS F IsInternal :=
  nems_iff_cat_or_internal.symm

theorem passAudit_no_external_selection
    (h : PassAudit F IsInternal) :
    ¬ NeedsExternalSelection F IsInternal :=
  (passAudit_iff_nems F IsInternal).mp h

theorem fails_audit_not_fundamental
    (h : NeedsExternalSelection F IsInternal) :
    ¬ NEMS F IsInternal :=
  fun hNEMS => hNEMS h

theorem audit_pass_categorical
    (h : F.ObsCategorical) :
    PassAudit F IsInternal :=
  Or.inl h

theorem audit_pass_selector
    (S : F.Selector) (hI : IsInternal S) :
    PassAudit F IsInternal :=
  Or.inr ⟨S, hI⟩

theorem audit_monotone
    (IsInternal' : F.Selector → Prop)
    (hweaken : ∀ S, IsInternal S → IsInternal' S)
    (h : PassAudit F IsInternal) :
    PassAudit F IsInternal' := by
  rcases h with hcat | ⟨S, hI⟩
  · exact Or.inl hcat
  · exact Or.inr ⟨S, hweaken S hI⟩

end Framework
end NemS
