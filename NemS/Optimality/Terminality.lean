import NemS.Core.Basics

/-!
# NemS.Optimality.Terminality

**Paper 18 (T1): The Theorem of Semantic Terminality.**

This module formalizes the end of reductionism in a PSC universe.
It proves that there exists a maximum depth of foundational physical description.
Any "deeper" theory `T'` extending a PSC-optimal theory `T` either fails
foundational status (by requiring new external selectors) or is physically redundant.
-/

namespace NemS
namespace Optimality

/-- A space of physical theories or foundational descriptions. -/
structure TheorySpace where
  Theory : Type
  /-- Descriptional complexity of a theory (e.g., algorithmic complexity K(T)). -/
  K : Theory → Nat
  /-- `RecordEquivalent T1 T2` means both theories predict the exact same
  macroscopic record facts (empirical equivalence at the record level). -/
  RecordEquivalent : Theory → Theory → Prop
  /-- `Extends T' T` means `T'` is a "deeper" or more detailed reductionist
  extension of `T` (adds micro-parameters). -/
  Extends : Theory → Theory → Prop
  /-- `FailsPSC T` means `T` requires external selectors not captured
  in the record language, violating Perfect Self-Containment (PSC). -/
  FailsPSC : Theory → Prop

namespace TheorySpace

variable {S : TheorySpace}

/-- **Premise 1:** If `T'` extends `T` with new micro-parameters, then either
these parameters don't change the macroscopic records (RecordEquivalent),
or if they do introduce unrecorded differences, they act as external
selectors (FailsPSC). -/
def ExtensionDichotomy (S : TheorySpace) : Prop :=
  ∀ T' T, S.Extends T' T → S.RecordEquivalent T' T ∨ S.FailsPSC T'

/-- **Premise 2:** Adding micro-parameters that do not change the record facts
strictly increases the descriptional complexity of the theory. -/
def ExtensionComplexity (S : TheorySpace) : Prop :=
  ∀ T' T, S.Extends T' T → S.RecordEquivalent T' T → S.K T < S.K T'

/-- **Definition:** A theory `T` is PSC-Optimal if it minimizes complexity
among all record-equivalent theories. -/
def PSCOptimal (S : TheorySpace) (T : S.Theory) : Prop :=
  ∀ T', S.RecordEquivalent T' T → S.K T ≤ S.K T'

/-- **Definition:** A theory `T'` is physically redundant relative to `T` if it
predicts the same records but is strictly more complex. -/
def Redundant (S : TheorySpace) (T' T : S.Theory) : Prop :=
  S.RecordEquivalent T' T ∧ S.K T < S.K T'

/-- **Theorem 18.1: Semantic Terminality.**

If `T` is a PSC-Optimal theory, any deeper extension `T'` either fails
PSC or is physically redundant.
-/
theorem semantic_terminality (S : TheorySpace)
    (h_dichotomy : S.ExtensionDichotomy)
    (h_complexity : S.ExtensionComplexity)
    (T : S.Theory) (_h_opt : S.PSCOptimal T)
    (T' : S.Theory) (h_ext : S.Extends T' T) :
    S.FailsPSC T' ∨ S.Redundant T' T := by
  cases h_dichotomy T' T h_ext with
  | inl h_req =>
    right
    exact ⟨h_req, h_complexity T' T h_ext h_req⟩
  | inr h_fails =>
    left
    exact h_fails

end TheorySpace
end Optimality
end NemS
