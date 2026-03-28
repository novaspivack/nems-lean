import SemanticSelfDescription.Theorems.NoFinalSelfTheory

/-!
# SemanticSelfDescription.Bridge.AugmentBarrierHypotheses

**Strengthen `CodeEquiv`** in `BarrierHypotheses` with a global **conjunct** `P` (typically a paper-side
hypothesis such as Layer‑1 representational obstruction), and **re-derive `hFP`** from the old fixed-point
witness + `P`.

This is **not** a universal `U123 → BarrierHypotheses` theorem: `P` and its proof `hP` are separate inputs.
When `hP` is taken from `b.reprBarrier` for `b : U123BarrierData A`, the packaged `BarrierHypotheses` depends
**essentially** on that barrier field (**reflexive** wrapper lives in `U123ReprAugmentedSemanticLink.lean`).
-/

set_option autoImplicit false

namespace SemanticSelfDescription

universe u v

variable {W : Type u} (F : SelfSemanticFrame W)

/--
Augment **`codeExt.CodeEquiv x y`** to **`bh.codeExt.CodeEquiv x y ∧ P`**, keep **`encoded`**, and re-prove **`hFP`**
by tagging the witness from **`bh.hFP`** with **`hP`**.

**Mathematical content:** whenever the fixed-point step already yielded **`codeExt.CodeEquiv d (F' d)`**, adding a
**global** conjunct **`P`** that does not depend on **`d`** is harmless for **`∃ d, …`**.
-/
def barrierHypotheses_augment_withGlobalConjunct (bh : BarrierHypotheses F) (P : Prop) (hP : P) :
    BarrierHypotheses F where
  codeExt :=
    { CodeEquiv := fun x y => bh.codeExt.CodeEquiv x y ∧ P
      decode_ext := fun hxy => bh.codeExt.decode_ext hxy.left }
  encoded := bh.encoded
  hFP := fun F' => by
    rcases bh.hFP F' with ⟨d, hd⟩
    exact ⟨d, ⟨hd, hP⟩⟩

end SemanticSelfDescription
