# Lean 4.29 / Mathlib v4.29.0-rc3 Upgrade — Disclosure

**Date:** March 2026  
**Scope:** nems-lean full codebase  
**Result:** All 176 Lean files build successfully. Zero new errors.

## 1. Audit Summary

A complete audit was performed on all Lean files in nems-lean for Lean 4.29 / Mathlib v4.29 compatibility:

- **Build status:** ✅ Success (1713 jobs, 0 errors)
- **Compatibility issues found:** None beyond those already fixed in `BuschGleason.lean`
- **Patterns checked:** `Finset.sum_apply`, `Matrix.sum_apply`, `norm_num`/`ring` with Complex, `linarith` with complex/real terms
- **Other modules:** Toy.lean, BICS.lean, Measures.lean, MatrixBasics.lean, EffectsStates.lean — all build without changes

## 2. BuschGleason.lean — Compatibility Fixes (Already Applied)

Three proofs in `NemS/Quantum/BuschGleason.lean` required tactical adjustments for Lean 4.29 / Mathlib v4.29. **No theorem or lemma statements were changed. No claims were weakened.**

### 2.1 `sum_to_normSq_Q` (line ~231)

**Issue:** `norm_num; ring` no longer closed the goal due to changes in how Lean 4.29 simplifies:
- Complex number literals `(1/2 : ℂ).re`, `Complex.re 2`, `Complex.im 2`, `(-Complex.I).im`
- `Nat.rawCast` in arithmetic expressions

**Fix:** Added explicit `have` lemmas to normalize these terms to their ℝ equivalents before applying `ring`. The mathematical identity proved is unchanged.

**Materiality:** Not material. Same identity; different proof script.

### 2.2 `diagEffects_sum_one` (line ~568)

**Issue:** `rw [Finset.sum_apply, Finset.sum_apply]` failed — the Finset.sum_apply API for sums of matrices changed in Mathlib 4.29.

**Fix:** Replaced with `rw [Matrix.sum_apply]`, which is the correct lemma for applying a sum of matrices at indices.

**Materiality:** Not material. Same equality; different Mathlib lemma (API compatibility).

### 2.3 `busch_gleason_unique` (line ~1071)

**Issue:** `linarith` failed to find a contradiction because hypotheses contained unsimplified complex/real literals (`Complex.re 2`, `Complex.normSq 2`, `(-Complex.I).im`, etc.) that linarith could not reduce.

**Fix:** Added `have` lemmas to normalize these numeric terms, then applied `simp only` with these lemmas to the hypotheses before `linarith`.

**Materiality:** Not material. Same uniqueness argument (diagEffect, realTestEff, imagTestEff); different tactic sequencing for numeric simplification.

## 3. Papers Affected

| Paper | Content | Update needed? |
|-------|---------|----------------|
| Paper 13 (Born Rule) | Describes busch_gleason_unique proof strategy | No. The proof strategy (diagEffect, realTestEff, imagTestEff) is unchanged. Build job count updated. |
| Paper 14 (BICS ⇒ NEMS) | States uniqueness is fully proved | No. Still accurate. |
| Paper 39 (GPT Probability) | References QuantumFinite | Already updated. |

## 4. No Weakening of Claims

- All theorem and lemma **statements** are identical.
- The **proof strategies** (entry-level equality via test effects) are unchanged.
- The **mathematical content** of the uniqueness theorem is unchanged.
- Zero new sorrys introduced; zero existing sorrys resolved by these fixes.

## 5. Recommendation

No advisor approval required for these changes: they are tactical/API compatibility fixes only. The mathematical claims and proof structure remain as originally verified.
