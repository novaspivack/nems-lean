import StructuralNonExhaustibility.Core.ReflexiveSystem
import SemanticSelfDescription.Core.SelfTheory
import SemanticSelfDescription.Theorems.NoFinalSelfTheory

/-!
# StructuralNonExhaustibility.Bridges.ToSemanticSelfDescription

**Semantic (Paper 51) → Program V `ReflexiveSystem`.**

This is the first **native NemS-side** `ReflexiveSystem` whose `BarrierHyp` and `TotalExhaustiveInternal`
carry genuine **semantic self-description** content (not the trivial `BarrierHyp := True` scaffold).

- **`reflexiveSystem_ofSelfSemanticFrame`** uses the same success predicate as the no-final-self-theory
  development: total exhaustive internalization = existence of a **final** internal self-theory.
- **`BarrierHyp := Nonempty (BarrierHypotheses F)`** matches the packaged barrier hypotheses used in
  **`no_final_self_theory'`** — **inhabited** hypotheses, not a raw unconstrained `Prop`.

**Sync requirement:** an `EngineNemsBarrierSync` still requires an **engine proof** that each
`U123BarrierData` point implies `Nonempty (BarrierHypotheses F)`. There is **no** definitional
implication from abstract paper U₁–U₃ packaging to **`BarrierHypotheses`**; that step is **honest
external mathematics** (e.g.base **`bh`** + **repr augmentation** via
`SemanticSelfDescription.Bridge.AugmentBarrierHypotheses` in the reflexive project).

**Predicated summit (Kleene / Rogers):** **`reflexiveSystem_ofSelfSemanticFramePred`** sets
**`BarrierHyp := Nonempty (BarrierHypothesesPred F P)`**. This matches computational routes that only assume
Rogers fixed points for a **class** of transformers **`P`** (e.g. **`Computable`**). **`NoTotalExhaustion`**
for that shell recovers from **`no_final_self_theory'`** only after **`∀ F', P F'`**, via
**`BarrierHypothesesPred.toBarrierHypotheses`**.

**Schema recovery:** `reflexiveSystem_ofSelfSemanticFrame_noTotalExhaustion` is **`NoTotalExhaustion`**
for this shell — Lemma **`no_final_self_theory'`**.
-/

set_option autoImplicit false

namespace StructuralNonExhaustibility

universe u v

variable {W : Type u}

/--
**Program V reflexive system** canonically associated to a **`SelfSemanticFrame`**.

`SelfInvolving` is **`selfSemanticTruth`**; **`TotalExhaustiveInternal`** is existence of a **final**
internal self-theory; **`BarrierHyp`** is **nonemptiness** of packaged **`BarrierHypotheses`**
(`NoFinalSelfTheory.lean`).
-/
def reflexiveSystem_ofSelfSemanticFrame (F : SemanticSelfDescription.SelfSemanticFrame W) :
    ReflexiveSystem.{u,v} where
  System := W
  Claim := F.Code
  SelfInvolving := F.selfSemanticTruth
  TotalExhaustiveInternal :=
    ∃ T : SemanticSelfDescription.InternalSelfTheory F, SemanticSelfDescription.FinalSelfTheory T
  BarrierHyp := Nonempty (SemanticSelfDescription.BarrierHypotheses F)

/--
**Predicated** Program V shell: **`BarrierHyp`** is nonemptiness of **`BarrierHypothesesPred F P`**.

**Universe note:** match **`BarrierHypothesesPred`** (Mathlib / Paper 51 wiring uses **`Code : Type 0`** for this bundle).
-/
def reflexiveSystem_ofSelfSemanticFramePred
    (F : SemanticSelfDescription.SelfSemanticFrame.{u, 0} W)
    (P : (F.Code → F.Code) → Prop) : ReflexiveSystem.{u, 0} where
  System := W
  Claim := F.Code
  SelfInvolving := F.selfSemanticTruth
  TotalExhaustiveInternal :=
    ∃ T : SemanticSelfDescription.InternalSelfTheory F, SemanticSelfDescription.FinalSelfTheory T
  BarrierHyp := Nonempty (SemanticSelfDescription.BarrierHypothesesPred (W := W) F P)

theorem reflexiveSystem_ofSelfSemanticFramePred_noTotalExhaustion_of_forall
    (F : SemanticSelfDescription.SelfSemanticFrame.{u, 0} W)
    (P : (F.Code → F.Code) → Prop)
    (hP : ∀ F' : F.Code → F.Code, P F') :
    (reflexiveSystem_ofSelfSemanticFramePred F P).NoTotalExhaustion := by
  intro hB hTot
  refine Nonempty.elim hB fun bh => ?_
  have bhTot :
      SemanticSelfDescription.BarrierHypotheses F :=
    SemanticSelfDescription.BarrierHypothesesPred.toBarrierHypotheses (F := F) (P := P) bh hP
  exact SemanticSelfDescription.no_final_self_theory' (F := F) bhTot hTot

theorem reflexiveSystem_ofSelfSemanticFrame_noTotalExhaustion
    (F : SemanticSelfDescription.SelfSemanticFrame W) :
    (reflexiveSystem_ofSelfSemanticFrame F).NoTotalExhaustion := by
  intro hB hTot
  rcases hB with ⟨bh⟩
  exact (SemanticSelfDescription.no_final_self_theory' (F := F) bh) hTot

/--
Corollary: from **any** witness of **`BarrierHypotheses`**, no final internal self-theory.
-/
theorem not_total_exhaustive_internal_of_barrier_hypotheses
    (F : SemanticSelfDescription.SelfSemanticFrame W) (bh : SemanticSelfDescription.BarrierHypotheses F) :
    ¬ ∃ T : SemanticSelfDescription.InternalSelfTheory F, SemanticSelfDescription.FinalSelfTheory T :=
  SemanticSelfDescription.no_final_self_theory' (F := F) bh

/--
Same conclusion from **`Nonempty (BarrierHypotheses F)`** (the `BarrierHyp` of
**`reflexiveSystem_ofSelfSemanticFrame`**).
-/
theorem not_total_exhaustive_internal_of_nonempty_barrier_hypotheses
    (F : SemanticSelfDescription.SelfSemanticFrame W)
    (h : Nonempty (SemanticSelfDescription.BarrierHypotheses F)) :
    ¬ ∃ T : SemanticSelfDescription.InternalSelfTheory F, SemanticSelfDescription.FinalSelfTheory T := by
  rcases h with ⟨bh⟩
  exact not_total_exhaustive_internal_of_barrier_hypotheses (F := F) bh

end StructuralNonExhaustibility
