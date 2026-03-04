import Mathlib.Data.Nat.Basic
import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Instances.Trivial
import Learning.Examples.ToyGuarantee

/-!
# Learning.Positive.Stratified

**Stratified self-certification (Paper 30).**

When the representability class R is **not** diagonally closed, the barrier's
hFP premise is not supplied by Reflection, so the barrier does not apply. In
that regime, total internal verifiers can exist for some claims. We connect to
Reflection's method-level separation (identity-only R is not diagonally closed)
and show a concrete case: the toy claim has a total decider at S_all. Thus
"bounded reflection" allows partial certification; diagonal closure is the
threshold beyond which total self-certification is impossible.
-/

set_option autoImplicit false

namespace Learning

namespace Positive

/-- **Stratified self-certification (toy)**: the toy claim has a total decider
at the "all functions" strength. The decider δ(n) := (n == 0) is total and
correct. This shows that in a regime where we do not assume hFP (e.g. when R
is not diagonally closed), total verifiers can exist. -/
theorem stratified_self_certification_toy :
    SelectorStrength.DecidableAt (SelectorStrength.S_all) Learning.Examples.ToyClaim := by
  refine ⟨fun n => n == 0, trivial, fun n => ?_⟩
  simp only [Learning.Examples.ToyClaim]
  exact match n with
  | 0 => by constructor <;> intro <;> rfl
  | m + 1 => by
      constructor
      · intro h
        have heq : (m + 1 == 0) = false := rfl
        rw [heq] at h
        exact False.elim (Bool.false_ne_true h)
      · intro h; exact False.elim (Nat.succ_ne_zero m h)

/- **Method-level separation (reference)**: In Reflection.Hierarchy.Separation,
the identity-only R on ℕ is proved not diagonally closed
(`not_diagClosed_identity_only`). In that regime the barrier's hFP is not
supplied by Reflection, so the barrier does not force absence of total
verifiers. Combined with `stratified_self_certification_toy`, this gives the
positive story: below the diagonal-closure threshold, total self-certification
can exist. -/

end Positive

end Learning
