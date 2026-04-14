import Mathlib.Computability.Halting
import Mathlib.Logic.Denumerable
import SemanticSelfDescription.Instances.GodelProvBic
import SemanticSelfDescription.Instances.KleenePartrec
import SemanticSelfDescription.Theorems.NoFinalSelfTheory

/-!
# SemanticSelfDescription.Theorems.SummitComparison

**Integration layer: predicated computational vs proof-theoretic full `BarrierHypotheses`.**

This module packages **precise** comparison statements between:

* the **Kleene / Rogers** line (**`kleene_computational_predicated_summit`**, **`BarrierHypothesesPred`** with
  **`P = kleeneComputableTransformerPred`** / **`Computable`**), and
* the **`ProvBic`** line (**`godelProvBicBarrierHypotheses`**, unconditional **`BarrierHypotheses`**), on a
  *different* unityped numerals frame (**Kleene predicated frame** vs **Gödel ProvBic frame**).

Key facts (no hand-waving):

1. **Shadow / downgrade:** any full **`BarrierHypotheses`** induces the **predicated-top** package
   **`BarrierHypothesesPred … (fun _ => True)`** via **`BarrierHypotheses.toPred`**.
2. **No universal computable upgrade on `ℕ → ℕ`:** not every transformer is **`Computable`** (Halting),
   hence the Kleene predicated witness **cannot** be promoted to unconditional **`BarrierHypotheses`**
   on the Kleene frame via **`BarrierHypothesesPred.toBarrierHypotheses`** — the needed
   **`∀ F', P F'`** hypothesis is **false** for **`P = kleeneComputableTransformerPred`**.
3. **Proof-theoretic side:** **`godelProvBicBarrierHypotheses.toPred`** is a **predicated-top** shadow of the
   proof-theoretic full summit, displaying what extra input **`ProvBicArithmeticalSemantics`** buys
   beyond the abstract **`GodelSystem`** shell.

Cross-refs: **`KleenePredicatedSummit`**, **`GodelProvBic`**, **(summit comparison)** (parent repo).
-/

set_option autoImplicit false

namespace SemanticSelfDescription

noncomputable section

open Computable ComputablePred Computable₂ Denumerable Encodable
open SelfReference.Instances
open Nat.Partrec.Code

/--
Not every **`ℕ → ℕ`** function is computable: otherwise Halting would be **`ComputablePred`** for
**`eval · n`**, contradicting Rice / **`halting_problem`**.
-/
theorem not_forall_computable_nat_to_nat : ¬∀ f : ℕ → ℕ, Computable f := by
  classical
  intro H
  let p : Nat.Partrec.Code → Prop := fun c => (eval c 0).Dom
  haveI : DecidablePred p := fun c => Classical.propDecidable _
  have hp : ComputablePred p := by
    refine computablePred_iff_computable_decide.mpr ?_
    let fDec : ℕ → ℕ := fun n => if p (ofNat Nat.Partrec.Code n) then 1 else 0
    have hfDec : Computable fDec := H fDec
    let F : Nat.Partrec.Code → ℕ := fun c => fDec (encode c)
    have hF : Computable F := hfDec.comp Computable.encode
    refine (Primrec.beq.to_comp.comp hF (Computable.const 1)).of_eq fun c => by
      have hFeq : F c = if p c then 1 else 0 := by simp [F, fDec, ofNat_encode]
      by_cases hpc : p c <;> simp [hFeq, hpc]
  exact halting_problem 0 hp

/--
The Kleene predicated class does **not** contain every code transformer: **`P F' :≡ Computable F'`**
fails universally on **`ℕ → ℕ`**.
-/
theorem not_forall_kleeneComputableTransformerPred :
    ¬∀ F' : kleenePartrecFrame.Code → kleenePartrecFrame.Code,
      kleeneComputableTransformerPred F' := by
  simpa [kleeneComputableTransformerPred, kleeneAsNatFn] using not_forall_computable_nat_to_nat

/--
**Shadow of a full barrier:** predicated hypotheses at **`P := ⊤`**.

This is the precise mathematical sense in which unconditional **`BarrierHypotheses`** is *at least as
strong* as any predicated package: it **determines** the top predicated instance.
-/
def barrierHypotheses_predicatedTopShadow {W : Type _} {F : SelfSemanticFrame W}
    (bh : BarrierHypotheses F) : BarrierHypothesesPred F (fun _ => True) :=
  bh.toPred

/--
The proof-theoretic full summit casts to **predicated-top** on the ProvBic frame — the **computational
shadow** in the sense of **`BarrierHypothesesPred`** with no restricting **`P`**.
-/
def godelProvBicBarrierHypotheses_predicatedTop (G : Godel.GodelSystem)
    (S : ProvBicArithmeticalSemantics G) :
    BarrierHypothesesPred (godelProvBicFrame G S) (fun _ => True) :=
  barrierHypotheses_predicatedTopShadow (godelProvBicBarrierHypotheses G S)

/--
**Obstruction to `toBarrierHypotheses` on the Kleene witness:** the universal side condition
**`∀ F', kleeneComputableTransformerPred F'`** is **false** — so the predicated computational summit
does **not** encode an unconditional **`BarrierHypotheses kleenePartrecFrame`** by **`toBarrierHypotheses`**
alone.

This is the formal counterpart of “**strict separation**” between the achieved predicated computational
route and full fixed-point closure on that same frame.
-/
theorem kleenePredicated_toBarrierHypotheses_side_condition_false :
    ¬∀ F' : kleenePartrecFrame.Code → kleenePartrecFrame.Code,
      kleeneComputableTransformerPred F' :=
  not_forall_kleeneComputableTransformerPred

end

end SemanticSelfDescription
