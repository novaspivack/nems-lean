import Mathlib.Tactic.ByContra
import SemanticSelfDescription.Core.Claims
import SemanticSelfDescription.Core.SelfTheory
import SemanticSelfDescription.Core.SelfErasure
import SemanticSelfDescription.Theorems.NoFinalSelfTheory

/-!
# SemanticSelfDescription.Theorems.SemanticRemainder

**Positive remainder theorem: reflexive closure requires remainder.**

Any internal self-theory either fails totality or leaves semantic remainder.
This is the positive formulation of non-self-erasure — not just a prohibition,
but a structural fact about what must remain.
-/

set_option autoImplicit false

namespace SemanticSelfDescription

universe u v

variable {W : Type u} (F : SelfSemanticFrame W)

open Verdict

/--
**Semantic remainder or nontotal.**

For any internally realized theory T under barrier hypotheses, either:
- T leaves semantic remainder (some code where verdict ≠ realized truth), or
- T is not total (abstains somewhere).

Equivalently: you cannot have both total and exact. The contrapositive of
no_final_self_theory.
-/
theorem semantic_remainder_or_nontotal
    (hB : BarrierHypotheses F) (T : InternalSelfTheory F)
    (hInt : T.internallyRealized) :
    SemanticRemainder F T ∨ ¬ TotalOn T := by
  by_contra hNot
  push_neg at hNot
  obtain ⟨hNoRem, hTotal⟩ := hNot
  have hExact : ExactOn T := fun code => by
    by_contra hBad
    exact hNoRem ⟨code, hBad⟩
  have hFinal : FinalSelfTheory T := ⟨hInt, hTotal, hExact⟩
  exact no_final_self_theory' F hB ⟨T, hFinal⟩

end SemanticSelfDescription
