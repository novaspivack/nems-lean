import Mathlib.Computability.PartrecCode
import Mathlib.Logic.Denumerable
import SemanticSelfDescription.Core.Claims
import SemanticSelfDescription.Theorems.NoFinalSelfTheory

/-!
# SemanticSelfDescription.Instances.KleenePartrec

**First closed computational frame (Kleene / `Nat.Partrec.Code`).**

See module docstring body in the repository history for the obstruction context (`Equiv = Eq`,
universal `CodeEquiv`, …). This file packages:

* **`kleenePartrecFrame`** — codes are `ℕ` (`encodeCode` / `ofNatCode`), claims are
  `Nat.Partrec.Code`, **`CodeEquiv`** is **extensional equality of `eval`**.
* **`kleeneComputationalBarrierHypotheses`** —
  **`BarrierHypothesesPred kleenePartrecFrame Computable`**, i.e. Rogers fixed points for
  **`Computable (ℕ → ℕ)`** maps on code numbers **only** (not for all set-theoretic `ℕ → ℕ`).

Reusable pattern for a later **`ProvBic`** line: keep **`BarrierHypothesesPred`** and swap the
predicate for “representable / provably-extensional” transformers once that witness exists.
-/

set_option autoImplicit false

namespace SemanticSelfDescription

noncomputable section

open Computable

/-- Extensional equivalence of program codes (Kleene / Rogers). -/
def kleeneCodeEquiv (a b : ℕ) : Prop :=
  ∀ x : ℕ,
    Nat.Partrec.Code.eval (Nat.Partrec.Code.ofNatCode a) x =
      Nat.Partrec.Code.eval (Nat.Partrec.Code.ofNatCode b) x

lemma eval_eq_of_kleeneCodeEquiv {a b : ℕ} (h : kleeneCodeEquiv a b) :
    Nat.Partrec.Code.eval (Nat.Partrec.Code.ofNatCode a) =
      Nat.Partrec.Code.eval (Nat.Partrec.Code.ofNatCode b) :=
  funext h

/-- Rogers / currying step for a map `F' : ℕ → ℕ` on code numbers. -/
def kleeneRogersCodeMap (F' : ℕ → ℕ) : Nat.Partrec.Code → Nat.Partrec.Code :=
  fun c => Nat.Partrec.Code.ofNatCode (F' (Nat.Partrec.Code.encodeCode c))

theorem kleeneRogersCodeMap_computable {F' : ℕ → ℕ} (hF : Computable F') :
    Computable (kleeneRogersCodeMap F') :=
  (Computable.ofNat Nat.Partrec.Code).comp (hF.comp Computable.encode)

theorem kleene_computational_hFP (F' : ℕ → ℕ) (hF : Computable F') :
    ∃ d : ℕ, kleeneCodeEquiv d (F' d) := by
  classical
  obtain ⟨c₀, hc₀⟩ :=
    @Nat.Partrec.Code.fixed_point (kleeneRogersCodeMap F') (kleeneRogersCodeMap_computable hF)
  use Nat.Partrec.Code.encodeCode c₀
  intro x
  have hdec : Nat.Partrec.Code.ofNatCode (Nat.Partrec.Code.encodeCode c₀) = c₀ := by
    simpa [Nat.Partrec.Code.ofNatCode_eq, Nat.Partrec.Code.encodeCode_eq] using
      Denumerable.ofNat_encode c₀
  have hx := congr_fun hc₀ x
  simp [kleeneRogersCodeMap] at hx
  exact (congr_arg (fun c => Nat.Partrec.Code.eval c x) hdec.symm).symm.trans hx.symm

/--
**Concrete Paper 51 semantics over partial\-recursive codes.**

`RealizedTrue c` means the program halts on input `0` with value `0`.
-/
def kleenePartrecFrame : SelfSemanticFrame Unit where
  Code := ℕ
  Claim := Nat.Partrec.Code
  decode := Nat.Partrec.Code.ofNatCode
  ClaimEquiv := fun c₁ c₂ => Nat.Partrec.Code.eval c₁ = Nat.Partrec.Code.eval c₂
  RealizedTrue := fun c => Nat.Partrec.Code.eval c 0 = Part.some 0
  truth_ext := fun {_ _} h => by rw [congr_fun h 0]

instance : EncodedNontrivial kleenePartrecFrame where
  code_true :=
    ⟨Nat.Partrec.Code.encodeCode Nat.Partrec.Code.zero,
      by
        have hdec : Nat.Partrec.Code.ofNatCode (Nat.Partrec.Code.encodeCode Nat.Partrec.Code.zero) =
            Nat.Partrec.Code.zero := by
          simpa [Nat.Partrec.Code.ofNatCode_eq, Nat.Partrec.Code.encodeCode_eq] using
            Denumerable.ofNat_encode Nat.Partrec.Code.zero
        simp only [SelfSemanticFrame.selfSemanticTruth, kleenePartrecFrame, hdec]
        rfl⟩
  code_false :=
    ⟨Nat.Partrec.Code.encodeCode (Nat.Partrec.Code.const 1),
      by
        intro h
        have hdec :
            Nat.Partrec.Code.ofNatCode (Nat.Partrec.Code.encodeCode (Nat.Partrec.Code.const 1)) =
              Nat.Partrec.Code.const 1 := by
          simpa [Nat.Partrec.Code.ofNatCode_eq, Nat.Partrec.Code.encodeCode_eq] using
            Denumerable.ofNat_encode (Nat.Partrec.Code.const 1)
        simp only [SelfSemanticFrame.selfSemanticTruth, kleenePartrecFrame, hdec,
          Nat.Partrec.Code.eval_const] at h
        exact Nat.one_ne_zero (Part.some_inj.mp h)⟩

/--
Code extensionality aligned with **extensional** equivalence of implementations.
-/
def kleeneCodeExtensional : CodeExtensional kleenePartrecFrame where
  CodeEquiv := kleeneCodeEquiv
  decode_ext := fun {_ _} hab =>
    eval_eq_of_kleeneCodeEquiv hab

/-- Coerce a code transformer to a bare `ℕ → ℕ` (definitional with `Code = ℕ`). -/
noncomputable abbrev kleeneAsNatFn (F' : kleenePartrecFrame.Code → kleenePartrecFrame.Code) :
    ℕ → ℕ :=
  F'

/-- Predicate: Kleene / Rogers fixed points are supplied for **`Computable`** maps `ℕ → ℕ`. -/
def kleeneComputableTransformerPred (F' : kleenePartrecFrame.Code → kleenePartrecFrame.Code) :
    Prop :=
  Computable (kleeneAsNatFn F')

/--
**Computational barrier hypotheses:** Rogers fixed points for **`Computable`** code transformers.
-/
def kleeneComputationalBarrierHypotheses :
    BarrierHypothesesPred kleenePartrecFrame kleeneComputableTransformerPred where
  codeExt := kleeneCodeExtensional
  encoded := inferInstance
  hFP F' hF := kleene_computational_hFP (kleeneAsNatFn F') hF

end

end SemanticSelfDescription
