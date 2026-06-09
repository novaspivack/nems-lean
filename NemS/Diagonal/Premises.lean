import NemS.Diagonal.ASR

/-!
# NemS.Diagonal.Premises

Named hypothesis bundles for transputation classification (PR1–PR5).
Physics premises enter as structure fields — never as bare axioms.
-/

namespace NemS
namespace Diagonal

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

/-- **PR1 (finite-witness / Σ₁ record-truth).**

`RT` is Σ₁⁰-definable: a computable witness predicate certifies truth
by a finite stage. Equivalently, `RT` is recursively enumerable.
-/
structure Sigma1RecordTruth {F : Framework} (asr : ASR F) where
  /-- Computable witness flag at stage `t`. -/
  witness : ℕ → ℕ → Bool
  witness_computable : Computable₂ witness
  /-- `RT n` holds iff some finite witness stage exists. -/
  witness_iff : ∀ n, asr.RT n ↔ ∃ t, witness n t = true

/-- Computable witness search flags for Σ₁ membership. -/
theorem Sigma1RecordTruth.witnessOption_computable {F : Framework} {asr : ASR F}
    (pr1 : Sigma1RecordTruth asr) :
    Computable₂ fun n t =>
      (if pr1.witness n t then some (0 : ℕ) else (none : Option ℕ)) :=
  (pr1.witness_computable.cond (Computable.const (some (0 : ℕ)))
      (Computable.const (none : Option ℕ))).of_eq
    fun p => by cases h : pr1.witness p.1 p.2 <;> simp [h]

noncomputable def Sigma1RecordTruth.witnessSearch {F : Framework} {asr : ASR F}
    (pr1 : Sigma1RecordTruth asr) : ℕ →. ℕ :=
  fun n => Nat.rfindOpt fun t =>
    if pr1.witness n t then some (0 : ℕ) else (none : Option ℕ)

theorem Sigma1RecordTruth.witnessSearch_partrec {F : Framework} {asr : ASR F}
    (pr1 : Sigma1RecordTruth asr) : Partrec (pr1.witnessSearch) :=
  (Partrec.rfindOpt pr1.witnessOption_computable).of_eq fun _ => rfl

theorem Sigma1RecordTruth.witnessSearch_dom_iff {F : Framework} {asr : ASR F}
    (pr1 : Sigma1RecordTruth asr) (n : ℕ) :
    (pr1.witnessSearch n).Dom ↔ ∃ t, pr1.witness n t = true := by
  classical
  dsimp [Sigma1RecordTruth.witnessSearch]
  rw [Nat.rfindOpt_dom]
  constructor
  · rintro ⟨t, _y, hmem⟩
    by_cases hw : pr1.witness n t
    · exact ⟨t, by simp [hw]⟩
    · simp [hw, Option.mem_def] at hmem
  · rintro ⟨t, hw⟩
    exact ⟨t, 0, by simp [Option.mem_def, hw]⟩

/-- `PR1` as Mathlib's `REPred` formulation of Σ₁⁰ membership. -/
def Sigma1RecordTruth.rePred {F : Framework} {asr : ASR F}
    (pr1 : Sigma1RecordTruth asr) : REPred asr.RT :=
  (pr1.witnessSearch_partrec.dom_re).of_eq fun n =>
    (pr1.witnessSearch_dom_iff n).trans (pr1.witness_iff n).symm

/-- **PR5 (record readout / branch labeling).**

At diagonal choice points, record-distinct branches are computably labeled
by the coded statement's truth bit; the label agrees with `RT`.
-/
structure RecordReadout {F : Framework} (asr : ASR F) where
  /-- Computable truth-bit label on record codes. -/
  label : ℕ → Bool
  label_computable : Computable label
  /-- The label tracks `RT` on the ASR encode-image. -/
  label_rt : ∀ (c : Code) (x : ℕ), label (asr.encode c x) = true ↔ asr.RT (asr.encode c x)

end Diagonal
end NemS
