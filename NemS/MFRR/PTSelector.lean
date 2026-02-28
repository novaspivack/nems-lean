import NemS.Core.Trichotomy
import NemS.Core.Selectors

/-!
# NemS.MFRR.PTSelector

Formalizes the *Transputation* (PT) operator as an internal selector
in the NEMS framework.

In MFRR, PT is the lawful, non-algorithmic adjudication principle that
resolves underdetermined continuations at choice points.  At the Lean
level, we represent PT structurally: it is a `Selector` that satisfies
the `IsInternal` predicate.  We do not encode MDL, Born rule, or
energetic content here — the bridge theorem is about *forced existence*
and *constraints on effectiveness*, not about the specific physics of
the adjudication.

The key results:
- `PT` bundles a selector with its internality witness.
- `nems_noncat_forces_PT`: under NEMS, non-categoricity forces PT to exist.
-/

namespace NemS
namespace MFRR

open NemS.Framework

/-- `PT` (Transputation) for framework `F` with internality predicate
`IsInternal` is an internal selector: a canonical-representative map
that is certified internal by the given predicate. -/
structure PT (F : Framework) (IsInternal : F.Selector → Prop) where
  /-- The underlying selector. -/
  selector : F.Selector
  /-- The selector is internal. -/
  internal : IsInternal selector

/-- Under NEMS, non-categoricity forces the existence of PT. -/
theorem nems_noncat_forces_PT
    {F : Framework} {IsInternal : F.Selector → Prop}
    (hNEMS : NEMS F IsInternal)
    (hNC : ¬ F.ObsCategorical) :
    ∃ _pt : PT F IsInternal, True := by
  obtain ⟨S, hI⟩ := nems_noncat_implies_internal hNEMS hNC
  exact ⟨⟨S, hI⟩, trivial⟩

/-- Under NEMS, the framework either is categorical or PT exists. -/
theorem nems_cat_or_PT
    {F : Framework} {IsInternal : F.Selector → Prop}
    (hNEMS : NEMS F IsInternal) :
    F.ObsCategorical ∨ ∃ _pt : PT F IsInternal, True := by
  rcases nems_implies_cat_or_internal hNEMS with hcat | ⟨S, hI⟩
  · exact Or.inl hcat
  · exact Or.inr ⟨⟨S, hI⟩, trivial⟩

end MFRR
end NemS
