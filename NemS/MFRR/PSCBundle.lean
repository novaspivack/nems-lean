import NemS.Core.Trichotomy
import NemS.Reduction.ER
import NemS.Visibility.SemanticExternality

/-!
# NemS.MFRR.PSCBundle

Packages the MFRR "Perfect Self-Containment" (PSC) condition as a
conjunction of NEMS-side closure assumptions.

PSC in MFRR says: "no external runner, no external evaluator, no external
model selector."  In the NEMS formalization this decomposes into:
- `NEMS F IsInternal` — no external model selection
- `ER` — externality reduction (external dependencies are model multiplicity)
- Semantic visibility — evaluator choices are record-visible

Rather than encoding PSC as a new primitive, we define it as the conjunction
of the already-proved NEMS conditions.  This makes PSC a *theorem-derived*
bundle rather than an axiom.
-/

namespace NemS
namespace MFRR

open NemS.Framework

/-- The PSC bundle for a framework `F` with internality predicate `IsInternal`.

This packages the three closure conditions that jointly constitute
Perfect Self-Containment in the NEMS formalization:
1. NEMS holds (no external model selection)
2. Every external dependency admits NEMS on the enlarged space
3. The framework satisfies determinacy-PSC (ER consequence) -/
structure PSCBundle (F : Framework) (IsInternal : F.Selector → Prop) where
  /-- NEMS holds for the base framework. -/
  nems : NEMS F IsInternal
  /-- Determinacy-PSC: every external dependency has an internal selector
      in the enlarged space. -/
  detPSC : F.DeterminacyPSC

/-- PSC implies NEMS (projection). -/
theorem PSCBundle.toNEMS {F : Framework} {IsInternal : F.Selector → Prop}
    (psc : PSCBundle F IsInternal) : NEMS F IsInternal :=
  psc.nems

/-- PSC implies determinacy-PSC (projection). -/
theorem PSCBundle.toDeterminacyPSC {F : Framework} {IsInternal : F.Selector → Prop}
    (psc : PSCBundle F IsInternal) : F.DeterminacyPSC :=
  psc.detPSC

/-- Under PSC, the framework is either categorical or has an internal selector. -/
theorem PSCBundle.cat_or_internal {F : Framework} {IsInternal : F.Selector → Prop}
    (psc : PSCBundle F IsInternal) :
    F.ObsCategorical ∨ ∃ S : F.Selector, IsInternal S :=
  nems_implies_cat_or_internal psc.nems

end MFRR
end NemS
