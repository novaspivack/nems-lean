import NemS.Diagonal.HaltingReduction
import NemS.Diagonal.Premises
import Mathlib.Computability.Reduce

/-!
# NemS.Diagonal.Sigma1Completeness

Σ₁⁰-completeness of record-truth on the diagonal fragment.

Under ASR + PR1 (`Sigma1RecordTruth`), `RT` is many-one equivalent to
the halting predicate. The hardness direction packages the certified
`halts_iff_RT` + `encode_computable` bridge; membership uses the
Σ₁ witness search.
-/

namespace NemS
namespace Diagonal

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

variable {F : Framework}

/-- Halting on input `n` is many-one reducible to `RT` via the ASR encoding.

This is the certified many-one reduction underlying Task 3 hardness:
`HALT ≤_m RT` with reduction `c ↦ encode c n`. -/
theorem halting_manyOne_reducible_to_RT (asr : ASR F) (n : ℕ) :
    (fun c : Code => (eval c n).Dom) ≤₀ asr.RT := by
  refine ⟨fun c => asr.encode c n, ?_, fun c => asr.halts_iff_RT c n⟩
  exact asr.encode_computable.comp Computable.id (Computable.const n)

/-- Witness search keyed on the first component of a paired input. -/
noncomputable def rtWitnessSearchPaired {asr : ASR F} (pr1 : Sigma1RecordTruth asr) :
    ℕ →. ℕ :=
  fun input => pr1.witnessSearch input.unpair.1

theorem rtWitnessSearchPaired_partrec {asr : ASR F} (pr1 : Sigma1RecordTruth asr) :
    Partrec (rtWitnessSearchPaired pr1) := by
  simpa [rtWitnessSearchPaired] using
    pr1.witnessSearch_partrec.comp (Computable.fst.comp Computable.unpair)

theorem rtWitnessSearchPaired_spec {asr : ASR F} (pr1 : Sigma1RecordTruth asr) (n : ℕ) :
    (rtWitnessSearchPaired pr1 (Nat.pair n 0)).Dom ↔ asr.RT n := by
  simpa [rtWitnessSearchPaired, Nat.unpair_pair] using
    (pr1.witnessSearch_dom_iff n).trans (pr1.witness_iff n).symm

noncomputable def rtWitnessCode {asr : ASR F} (pr1 : Sigma1RecordTruth asr) : Code :=
  (Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.mp (rtWitnessSearchPaired_partrec pr1))).choose

theorem rtWitnessCode_spec {asr : ASR F} (pr1 : Sigma1RecordTruth asr) (n : ℕ) :
    (eval (rtWitnessCode pr1) (Nat.pair n 0)).Dom ↔ asr.RT n := by
  classical
  have hspec :=
    (Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.mp (rtWitnessSearchPaired_partrec pr1))).choose_spec
  have hdom : (eval (rtWitnessCode pr1) (Nat.pair n 0)).Dom ↔
      (rtWitnessSearchPaired pr1 (Nat.pair n 0)).Dom := by
    dsimp [rtWitnessCode]
    simpa using congrArg (fun g => (g (Nat.pair n 0)).Dom) hspec
  exact hdom.trans (rtWitnessSearchPaired_spec pr1 n)

/-- `RT` is many-one reducible to halting at input `0`.

The reduction maps `n` to the witness-search code specialized at `n`,
then reads halting at argument `0`. -/
theorem rt_manyOne_reducible_to_halting_zero {asr : ASR F}
    (pr1 : Sigma1RecordTruth asr) :
    asr.RT ≤₀ (fun c : Code => (eval c 0).Dom) := by
  refine ⟨fun n => Nat.Partrec.Code.curry (rtWitnessCode pr1) n, ?_, fun n => ?_⟩
  · exact Primrec₂.to_comp Nat.Partrec.Code.primrec₂_curry |>.comp
      (Computable.const (rtWitnessCode pr1)) Computable.id
  · simpa [Nat.Partrec.Code.eval_curry] using (rtWitnessCode_spec pr1 n).symm

/-- **Σ₁⁰-completeness of record-truth on the diagonal fragment (Lemma 1).**

Under ASR + PR1, `RT` is many-one equivalent to the halting predicate at
input `0`; hence `RT` is Σ₁⁰-complete and not computably decidable. -/
theorem rt_sigma1_complete_on_diagonal {asr : ASR F} (pr1 : Sigma1RecordTruth asr) :
    ManyOneEquiv asr.RT (fun c : Code => (eval c 0).Dom) :=
  ⟨rt_manyOne_reducible_to_halting_zero pr1, halting_manyOne_reducible_to_RT asr 0⟩

theorem rt_sigma1_not_computable {asr : ASR F} (_pr1 : Sigma1RecordTruth asr) :
    ¬ ComputablePred asr.RT :=
  asr_rt_not_computable asr

theorem rt_sigma1_complete_not_delta1 {asr : ASR F} (pr1 : Sigma1RecordTruth asr) :
    ¬ ComputablePred asr.RT ∧ REPred asr.RT :=
  ⟨rt_sigma1_not_computable pr1, pr1.rePred⟩

end Diagonal
end NemS
