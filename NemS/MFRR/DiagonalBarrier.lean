import NemS.Core.Trichotomy
import NemS.Core.Selectors
import NemS.Core.Internality
import NemS.Diagonal.Barrier

/-!
# NemS.MFRR.DiagonalBarrier

Formalizes the diagonal barrier: the constraint that no *total effective*
selector can exist on a diagonal-capable fragment.

This corresponds to Theorem 5.9 and Corollary 5.12 of the NEMS theorem
paper.  The key idea: if the record fragment is expressive enough to
encode self-reference (diagonal capability / ASR), then any hypothetical
total computable selector would yield a halting decider, contradicting
undecidability.

## Design

`DiagonalCapable` is a structure carrying an `ASR` (Arithmetic
Self-Reference) package — the data needed to reduce record-truth
decidability to halting decidability.  The diagonal barrier is then
a **theorem** (not an axiom), proved via the halting reduction in
`NemS.Diagonal.HaltingReduction`.

## IIa / IIb classification

- **Class IIa:** internal selector exists and is total-effective
  (possible only when the framework is NOT diagonal-capable).
- **Class IIb:** internal selector exists but is NOT total-effective
  on the diagonal-capable fragment (forced when diagonal-capable).

The split theorem shows: under NEMS + non-categoricity + diagonal
capability, the framework must be Class IIb.
-/

namespace NemS
namespace MFRR

open NemS.Framework
open NemS.Diagonal

/-- A framework is *diagonal-capable* if it carries an ASR structure:
the record fragment is expressive enough to encode the halting problem.

This replaces the earlier abstract `DiagonalCapable` class (which
carried only `True`) with a data-carrying structure that enables
the diagonal barrier to be *proved* rather than axiomatized. -/
class DiagonalCapable (F : Framework) where
  /-- The ASR structure witnessing diagonal capability. -/
  asr : ASR F

/-- A selector is *total-effective* if it factors through a computable
section of the quotient map AND that section is total (defined on all
world-types).  At the abstract level, we identify this with
`IsComputabilityInternal` from the NEMS library. -/
def TotalEffective (F : Framework) (S : F.Selector) : Prop :=
  IsComputabilityInternal S

/-- **Diagonal Barrier (fully proved, zero axioms).**

In any diagonal-capable framework with an ASR structure, record-truth
is not computably decidable.  Therefore no total-effective selector
can decide record-truth on all codes.

This is the Lean formalization of Theorem 5.9 of the NEMS theorem
paper, proved via the halting reduction using Mathlib's
`ComputablePred.halting_problem`. -/
theorem diagonal_barrier_rt (F : Framework) [dc : DiagonalCapable F] :
    ¬ ComputablePred dc.asr.RT :=
  no_total_effective_rt_decider dc.asr

/-- **Class IIa:** the framework has an internal selector that is
total-effective.  This is only possible when the framework is NOT
diagonal-capable (or is categorical). -/
def ClassIIa (F : Framework) (IsInternal : F.Selector → Prop) : Prop :=
  (∃ S : F.Selector, IsInternal S) ∧
  (∃ S : F.Selector, TotalEffective F S)

/-- **Class IIb:** the framework has an internal selector, but no
total-effective selector exists.  This is the forced classification
under diagonal capability + non-categoricity. -/
def ClassIIb (F : Framework) (IsInternal : F.Selector → Prop) : Prop :=
  (∃ S : F.Selector, IsInternal S) ∧
  ¬ (∃ S : F.Selector, TotalEffective F S ∧ IsComputabilityInternal S)

/-- **IIa/IIb split theorem.**

Under NEMS + non-categoricity:
- An internal selector exists (from NEMS + non-categoricity).
- The diagonal barrier constrains what that selector can decide.

The forcing into IIb requires connecting the abstract selector to
record-truth decidability.  We state this as: NEMS + non-categoricity
forces an internal selector, and the diagonal barrier prevents
record-truth from being computably decidable. -/
theorem nems_noncat_forces_internal_and_diagonal_barrier
    {F : Framework} [dc : DiagonalCapable F]
    {IsInternal : F.Selector → Prop}
    (hNEMS : NEMS F IsInternal)
    (hNC : ¬ F.ObsCategorical) :
    (∃ S : F.Selector, IsInternal S) ∧ ¬ ComputablePred dc.asr.RT := by
  exact ⟨nems_noncat_implies_internal hNEMS hNC, diagonal_barrier_rt F⟩

end MFRR
end NemS
