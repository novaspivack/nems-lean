import NemS.Core.Basics
import NemS.MFRR.PTSelector

/-!
# NemS.Adjudication.Basic

Core definitions for the No-Emulation theorem (Paper 15).

A *choice point* in a framework is a state where the adjudicator (PT)
must make a non-deterministic selection among multiple continuations.
The *adjudication function* is the PT selector restricted to those states.

These definitions extend the existing PT/selector infrastructure from
`NemS.MFRR.PTSelector` with the choice-point interface needed to state
the No-Emulation theorem precisely.
-/

namespace NemS
namespace Adjudication

open NemS.Framework

/-- A *choice-point interface* for framework `F` picks out the states
where PT must actively select among multiple continuations.

- `isChoicePoint` : the predicate identifying choice-point states.
- `alternatives`  : for each choice-point state, the set of valid
  continuations that PT may select from.

This is the Lean surrogate for `ChoicePointInterface(F)` in the
Paper 15 roadmap spec. -/
structure ChoicePointInterface (F : Framework) where
  /-- Predicate: `isChoicePoint s` iff `s` is a state requiring active selection. -/
  isChoicePoint : F.Model → Prop
  /-- The set of valid continuations at a choice-point state. -/
  alternatives  : F.Model → Set F.Model

/-- An *adjudication function* for a choice-point interface `C` is a
function `select : F.Model → F.Model` that:
- at choice-point states, picks from the valid alternatives;
- at non-choice-point states, acts as the identity (deterministic update). -/
structure AdjudicationFn (F : Framework) (C : ChoicePointInterface F) where
  /-- The selection function. -/
  select : F.Model → F.Model
  /-- At choice points, the selection must lie in the alternatives. -/
  valid_at_choice  : ∀ s, C.isChoicePoint s → select s ∈ C.alternatives s
  /-- At non-choice points, the selection is the identity. -/
  valid_off_choice : ∀ s, ¬ C.isChoicePoint s → select s = s

end Adjudication
end NemS
