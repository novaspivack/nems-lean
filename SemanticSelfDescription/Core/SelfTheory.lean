import SemanticSelfDescription.Core.Claims
import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Instances.Trivial

/-!
# SemanticSelfDescription.Core.SelfTheory

**Internal self-theories and finality (Necessary Incompleteness of Self-Description).**

An `InternalSelfTheory` is an internally realized theory that assigns verdicts
to self-semantic claims. A **final** self-theory is total, faithful, and exact
on the entire encoded claim family — the theorem shows no such theory can exist
when the frame is diagonally capable.

## Key definitions

- `Verdict` : yes / no / abstain
- `InternalSelfTheory` : theory with verdict function
- `TotalOn`, `FaithfulOn`, `ExactOn`, `FinalSelfTheory`
- `theoryBoolPred` : the Bool predicate induced by a theory
-/

set_option autoImplicit false

namespace SemanticSelfDescription

universe u v

variable {W : Type u} (F : SelfSemanticFrame W)

/--
Verdicts issued by an internal self-theory.
- `yes` : theory asserts claim is realized-true
- `no` : theory asserts claim is not realized-true
- `abstain` : theory leaves claim open

For final theories, abstain is ruled out.
-/
inductive Verdict
  | yes
  | no
  | abstain
  deriving DecidableEq, Repr

open Verdict

/--
An **internal self-theory** for world `W` over frame `F`.

- `verdict` maps codes of self-semantic claims to a verdict
- `internallyRealized` : the theory is definable/realized within the world's
  representational resources (bridged to Closure when needed)
-/
structure InternalSelfTheory where
  verdict   : F.Code → Verdict
  internallyRealized : Prop

/-- `T` answers every encoded claim without abstention. -/
def TotalOn {W : Type u} {F : SelfSemanticFrame W} (T : InternalSelfTheory F) : Prop :=
  ∀ code : F.Code, T.verdict code ≠ abstain

/--
Faithfulness / soundness: verdicts agree with realized truth.
-/
def FaithfulOn {W : Type u} {F : SelfSemanticFrame W} (T : InternalSelfTheory F) : Prop :=
  ∀ code : F.Code,
    match T.verdict code with
    | yes     => F.RealizedTrue (F.decode code)
    | no      => ¬ F.RealizedTrue (F.decode code)
    | abstain => True

/--
Exactness: theory answers yes iff realized-true, no iff realized-false.
Equivalent to TotalOn ∧ FaithfulOn for two-valued verdicts.
-/
def ExactOn {W : Type u} {F : SelfSemanticFrame W} (T : InternalSelfTheory F) : Prop :=
  ∀ code : F.Code,
    (T.verdict code = yes ↔ F.RealizedTrue (F.decode code)) ∧
    (T.verdict code = no  ↔ ¬ F.RealizedTrue (F.decode code))

/--
A **final** self-theory is internal, total, and exact on the entire encoded
self-semantic claim family.
-/
def FinalSelfTheory {W : Type u} {F : SelfSemanticFrame W} (T : InternalSelfTheory F) : Prop :=
  T.internallyRealized ∧ TotalOn (F := F) T ∧ ExactOn (F := F) T

/--
The Bool predicate induced by a theory (for connection to SelectorStrength).
Abstain maps to false; for total theories this is harmless.
-/
def theoryBoolPred {W : Type u} {F : SelfSemanticFrame W} (T : InternalSelfTheory F) : F.Code → Bool :=
  fun code =>
    match T.verdict code with
    | yes     => true
    | no      => false
    | abstain => false

/--
For a final theory, the induced Bool predicate is a total decider for
self-semantic truth.
-/
theorem finalTheory_induces_totalDecider
    (T : InternalSelfTheory F) (hT : FinalSelfTheory T) :
    SelectorStrength.TotalDecider F.selfSemanticTruth (theoryBoolPred T) := by
  intro code
  rcases hT with ⟨_, hTotal, hExact⟩
  have hEx := hExact code
  constructor
  · intro h
    by_cases heq : T.verdict code = yes
    · exact hEx.1.mp heq
    · have hFalse : theoryBoolPred T code = false := by
        simp only [theoryBoolPred]
        cases h : T.verdict code with
        | yes => exact False.elim (absurd h heq)
        | no => rfl
        | abstain => rfl
      rw [hFalse] at h
      exact False.elim (Bool.false_ne_true h)
  · intro hTrue
    have hYes := hEx.1.mpr hTrue
    simp only [theoryBoolPred, hYes]

/--
A final self-theory induces DecidableAt S_all for self-semantic truth.
(S_all accepts all functions, so we just need the TotalDecider.)
-/
theorem finalTheory_induces_decidableAt
    (T : InternalSelfTheory F) (hT : FinalSelfTheory T) :
    SelectorStrength.DecidableAt SelectorStrength.S_all F.selfSemanticTruth :=
  ⟨theoryBoolPred T, trivial, finalTheory_induces_totalDecider F T hT⟩

/--
Final theories never abstain. (Useful normalization.)
-/
theorem finalTheory_no_abstain
    (T : InternalSelfTheory F) (hT : FinalSelfTheory T) :
    ∀ code : F.Code, T.verdict code ≠ abstain :=
  hT.2.1

end SemanticSelfDescription
