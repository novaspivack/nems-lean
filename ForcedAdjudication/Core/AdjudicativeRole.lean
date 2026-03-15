import NemS.MFRR.BridgeToNEMS

/-!
# ForcedAdjudication.Core.AdjudicativeRole

Forced adjudicative role: PSC + choice ⇒ internal selector (Program IV).
Re-exports and packages NemS.MFRR.PSC_and_choice_force_PT.
-/

set_option autoImplicit false

namespace ForcedAdjudication

open NemS NemS.MFRR NemS.Framework

/-- **Forced adjudicative role theorem.**
Under PSC and record-divergent choice, an internal selector (PT) exists.
This is the structural necessity of adjudication: closure + choice forces it. -/
theorem forced_adjudicative_role
    {F : Framework} {IsInternal : F.Selector → Prop}
    (psc : PSCBundle F IsInternal)
    (cd : ChoiceData F)
    (hChoice : HasRecordDivergentChoice F cd) :
    ∃ _pt : PT F IsInternal, True :=
  PSC_and_choice_force_PT psc cd hChoice

/-- **Internal selector extraction.** -/
theorem forced_adjudicative_role_selector
    {F : Framework} {IsInternal : F.Selector → Prop}
    (psc : PSCBundle F IsInternal)
    (cd : ChoiceData F)
    (hChoice : HasRecordDivergentChoice F cd) :
    ∃ S : F.Selector, IsInternal S :=
  PSC_and_choice_force_internal_selector psc cd hChoice

end ForcedAdjudication
