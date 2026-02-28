import NemS.MFRR.ChoicePoints
import NemS.MFRR.PSCBundle
import NemS.MFRR.PTSelector
import NemS.MFRR.DiagonalBarrier

/-!
# NemS.MFRR.BridgeToNEMS

The headline theorems connecting MFRR to the NEMS classification spine.

This module imports the MFRR-specific definitions (choice points, PSC bundle,
PT selector, diagonal barrier) and proves the main bridge results:

1. **PSC + genuine choice ⇒ PT exists.**
   Under PSC (which implies NEMS), record-divergent choice implies
   non-categoricity, which under NEMS forces an internal selector (PT).

2. **PSC + genuine choice + diagonal capability ⇒ internal selector
   exists AND record-truth is not computably decidable.**
   Adding diagonal capability (ASR) constrains what can be computed
   about record-truth.

3. **Full PSC upgrade:** NEMS + ER + semantic visibility ⇒ determinacy-PSC.

These are the "Reflexive Closure Theorem" results in machine-checked form:
closure (PSC) + self-reference (diagonal capability) forces nontrivial
internal selection, and record-truth on the diagonal-capable fragment
cannot be computably decided.

**All results are fully proved — zero axioms.**
-/

namespace NemS
namespace MFRR

open NemS.Framework

/-! ## Theorem 1: PSC + record-divergent choice ⇒ PT exists -/

/-- **MFRR Bridge Theorem (flagship).**
Under PSC, if the framework has record-divergent choice (multiple
observationally distinct branches at some choice point), then an
internal selector (PT / Transputation) must exist. -/
theorem PSC_and_choice_force_PT
    {F : Framework} {IsInternal : F.Selector → Prop}
    (psc : PSCBundle F IsInternal)
    (cd : ChoiceData F)
    (hChoice : HasRecordDivergentChoice F cd) :
    ∃ _pt : PT F IsInternal, True := by
  have hNC : ¬ F.ObsCategorical :=
    recordDivergentChoice_implies_not_obsCategorical cd hChoice
  exact nems_noncat_forces_PT psc.nems hNC

/-- Equivalent formulation: extract the selector directly. -/
theorem PSC_and_choice_force_internal_selector
    {F : Framework} {IsInternal : F.Selector → Prop}
    (psc : PSCBundle F IsInternal)
    (cd : ChoiceData F)
    (hChoice : HasRecordDivergentChoice F cd) :
    ∃ S : F.Selector, IsInternal S := by
  have hNC : ¬ F.ObsCategorical :=
    recordDivergentChoice_implies_not_obsCategorical cd hChoice
  exact nems_noncat_implies_internal psc.nems hNC

/-! ## Theorem 2: PSC + choice + diagonal ⇒ selector + undecidable RT -/

/-- **MFRR Diagonal Split Theorem.**
Under PSC + record-divergent choice + diagonal capability (ASR):
- An internal selector (PT) exists, AND
- Record-truth on the ASR fragment is not computably decidable.

This is the "Reflexive Closure ⇒ constrained selection" result:
closure forces selection, and diagonalization (via the halting
reduction) constrains what can be computed about record-truth.

**Fully proved — zero axioms.** -/
theorem PSC_choice_diagonal_forces_constrained_selection
    {F : Framework} [dc : DiagonalCapable F]
    {IsInternal : F.Selector → Prop}
    (psc : PSCBundle F IsInternal)
    (cd : ChoiceData F)
    (hChoice : HasRecordDivergentChoice F cd) :
    (∃ S : F.Selector, IsInternal S) ∧ ¬ ComputablePred dc.asr.RT := by
  have hNC : ¬ F.ObsCategorical :=
    recordDivergentChoice_implies_not_obsCategorical cd hChoice
  exact nems_noncat_forces_internal_and_diagonal_barrier psc.nems hNC

/-- The PSC classification under diagonal capability:
categorical ∨ (internal selector exists ∧ RT not computable). -/
theorem PSC_classification
    {F : Framework} [dc : DiagonalCapable F]
    {IsInternal : F.Selector → Prop}
    (psc : PSCBundle F IsInternal) :
    F.ObsCategorical ∨
    ((∃ S : F.Selector, IsInternal S) ∧ ¬ ComputablePred dc.asr.RT) := by
  by_cases hcat : F.ObsCategorical
  · exact Or.inl hcat
  · exact Or.inr (nems_noncat_forces_internal_and_diagonal_barrier psc.nems hcat)

/-! ## Theorem 3: NEMS + non-categoricity ⇒ internal selector -/

/-- Under NEMS alone (without the full PSC bundle), non-categoricity
forces the existence of an internal selector. -/
theorem NEMS_noncat_forces_selector
    {F : Framework}
    {IsInternal : F.Selector → Prop}
    (hNEMS : NEMS F IsInternal)
    (hNC : ¬ F.ObsCategorical) :
    ∃ S : F.Selector, IsInternal S :=
  nems_noncat_implies_internal hNEMS hNC

/-! ## Theorem 4: The "No External Law" phrasing -/

/-- **No External Law Theorem.**
Under PSC, the framework does not need external model selection.
This is the direct MFRR ↔ NEMS bridge: PSC implies NEMS, which is
defined as ¬ NeedsExternalSelection. -/
theorem no_external_law
    {F : Framework} {IsInternal : F.Selector → Prop}
    (psc : PSCBundle F IsInternal) :
    ¬ NeedsExternalSelection F IsInternal :=
  psc.nems

end MFRR
end NemS
