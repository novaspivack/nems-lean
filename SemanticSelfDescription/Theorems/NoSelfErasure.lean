import SemanticSelfDescription.Core.Claims
import SemanticSelfDescription.Core.SelfTheory
import SemanticSelfDescription.Core.SelfScope
import SemanticSelfDescription.Core.SelfErasure
import SemanticSelfDescription.Theorems.NoFinalSelfTheory

/-!
# SemanticSelfDescription.Theorems.NoSelfErasure

**Non-Self-Erasure Theorem: Reflexive Closure Requires Semantic Remainder.**

The ladder of no-self-erasure theorems, from weak (final + self-scoped) to strong
(semantic closure by theory). A reflexive system may close over itself, but it
cannot erase the distinction between itself and its own self-representation.

## Theorem ladder

- `no_weak_self_erasure` : ¬ ∃ T, WeakSelfErasing T (immediate from no_final_self_theory)
- `strong_self_erasing_implies_final` : StrongSelfErasing T → FinalSelfTheory T
- `no_strong_self_erasure` : ¬ ∃ T, StrongSelfErasing T (flagship)
-/

set_option autoImplicit false

namespace SemanticSelfDescription

universe u v

variable {W : Type u} (F : SelfSemanticFrame W)

open Verdict

/--
**Theorem 1. Weak no-self-erasure.**

A weak self-erasing theory (final + self-scoped) cannot exist under barrier hypotheses.
Immediate corollary of no_final_self_theory.
-/
theorem no_weak_self_erasure (hB : BarrierHypotheses F) :
    ¬ ∃ T : InternalSelfTheory F, WeakSelfErasing F T := by
  intro ⟨T, hW⟩
  obtain ⟨w⟩ := hW
  exact no_final_self_theory' F hB ⟨T, w.final⟩

/--
**Theorem 2. Strong self-erasure implies final self-theory.**

Structural: any strong self-erasing theory is a fortiori final.
-/
theorem strong_self_erasing_implies_final {T : InternalSelfTheory F} :
    StrongSelfErasing F T → FinalSelfTheory T := by
  intro hSE
  obtain ⟨s⟩ := hSE
  exact s.closure.final

/--
**Theorem 3. No strong self-erasure.**

No internal theory can exhaust the realized semantic totality while remaining
closed under self-application. The flagship non-self-erasure theorem.

In slogan form: **The snake can see its tail, but it cannot swallow itself.**
-/
theorem no_strong_self_erasure (hB : BarrierHypotheses F) :
    ¬ ∃ T : InternalSelfTheory F, StrongSelfErasing F T := by
  intro ⟨T, hSE⟩
  obtain ⟨s⟩ := hSE
  exact no_final_self_theory' F hB ⟨T, s.closure.final⟩

end SemanticSelfDescription
