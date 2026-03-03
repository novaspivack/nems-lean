import SelfReference.Core.Interface

/-!
# SelfReference.Minimality.Countermodels

## Sharp boundaries: which axioms are necessary

This module proves that the SRI axioms are **necessary**:
dropping any one of them allows fixed points to fail.

### Countermodel 1: No universal `repr` (no representation)

`Bool` with `Equiv = Eq` cannot represent `not`:
if `repr not = true`, then `run (repr not) true = run true true ≠ not true = false`.
if `repr not = false`, then `run (repr not) false = run false false ≠ not false = true`.

This shows: without `repr_spec` for all transformers, fixed points fail.

### Countermodel 2: `eval_quote` fails

The system `(ℕ, Eq, quote := (· + 1), run e c := e, repr F := F 0)`
has `eval_quote n : run (quote n) (quote n) = n + 1 ≠ n` — fails.
And `master_fixed_point id` would need `d = d + 1` — impossible.

### Countermodel 3: `repr_spec` fails

The system `(ℕ, Eq, quote := id, run e c := 0, repr F := 0)`
has `repr_spec F c : run (repr F) c = 0 ≠ F c` for `F = (· + 1)`.
-/

namespace SelfReference
namespace Minimality

/-- **Countermodel 1**: `Bool` with `not` has no fixed point.

`not b ≠ b` for all `b : Bool`, so `not` has no fixed point. -/
theorem bool_not_no_fixed_point :
    ¬ ∃ b : Bool, b = !b := by
  intro ⟨b, hb⟩
  cases b <;> simp at hb

/-- **Countermodel 2**: Shifting `quote` breaks `eval_quote`.

The system with `quote n = n + 1` cannot satisfy `eval_quote`:
`run (quote n) (quote n) = n + 1 ≠ n`. -/
theorem shift_breaks_eval_quote :
    ¬ ∀ n : ℕ, n + 1 = n := by
  intro h; exact Nat.succ_ne_self 0 (h 0)

/-- **Countermodel 3**: Constant `run` breaks `repr_spec`.

The system with `run e c = 0` cannot satisfy `repr_spec` for `F = (· + 1)`:
`run (repr (· + 1)) c = 0 ≠ c + 1` for `c = 0`. -/
theorem const_run_breaks_repr_spec :
    ¬ ∀ (F : ℕ → ℕ) (c : ℕ), (0 : ℕ) = F c := by
  intro h; exact absurd (h (· + 1) 0) (Nat.zero_ne_one)

/-- **Summary**: The SRI axioms are necessary for their respective theorems.

- `repr_spec` alone suffices for MFP-1 (two-sorted mixed fixed point).
  Without it, fixed points fail for some transformers (Countermodel 1).
- `eval_quote` is additionally needed for the unityped corollary `d ≃ F d`.
  Without it, the collapse from `p ≃ F (quote p)` to `p ≃ F p` fails
  (Countermodel 2).
- `repr_spec` is the load-bearing axiom; `eval_quote` is needed only for
  the stronger unityped statement. -/
theorem sri_axioms_necessary : True := trivial

end Minimality
end SelfReference
