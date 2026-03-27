import NemS.Physical.ASRFromUCT

/-!
# NemS.Physical.Instantiation

Concrete instantiation demonstrating that PhysUCT is satisfiable.

We use the same "halting framework" from `NemS/Diagonal/Instantiation.lean`
but present it as a PhysUCT instance rather than directly as ASR.
This demonstrates that the PhysUCT premise ("computers exist and halting
is record-expressible") is not exotic.
-/

namespace NemS
namespace Physical

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- The halting framework (as a PhysUCT instance):
natural numbers index programs, halting is record-truth. -/
def haltingFramework : Framework where
  Model := ℕ
  Rec := ℕ
  Truth := fun m r => (eval (Denumerable.ofNat Code m) r).Dom

/-- PhysUCT instance for the halting framework. -/
noncomputable def haltingPhysUCT : PhysUCT haltingFramework where
  RT := fun n => (eval (Denumerable.ofNat Code n.unpair.1) n.unpair.2).Dom
  encode := fun c x => Nat.pair (Encodable.encode c) x
  encode_computable :=
    Computable.pair
      (Computable.encode.comp Computable.fst)
      Computable.snd
  halts_iff_RT := fun c x => by
    simp only [Nat.unpair_pair]
    rw [Denumerable.ofNat_encode c]

/-- The halting framework is diagonal-capable via PhysUCT. -/
@[reducible]
noncomputable def haltingFramework_diagonalCapable :
    NemS.MFRR.DiagonalCapable haltingFramework :=
  physUCT_implies_diagonalCapable haltingPhysUCT

/-- Consistency check: the diagonal barrier applies. -/
theorem haltingFramework_RT_not_computable :
    ¬ ComputablePred haltingPhysUCT.RT :=
  physUCT_implies_RT_not_computable haltingPhysUCT

/-! ### Semantic glue (SPEC_025) — existential **`Truth`** grid ↔ existential **`RT`** -/

/-- On the halting grid, “some `Truth` instance” is the same as “some `PhysUCT.RT` code,” via `Nat.pair` /
  `unpair` (same `eval … Dom` content). -/
theorem haltingFramework_exists_truth_iff_exists_physUCT_rt :
    (∃ m : haltingFramework.Model, ∃ r : haltingFramework.Rec, haltingFramework.Truth m r) ↔
      ∃ n : ℕ, haltingPhysUCT.RT n := by
  constructor
  · rintro ⟨m, r, h⟩
    refine ⟨Nat.pair m r, ?_⟩
    simpa [haltingPhysUCT, Nat.unpair_pair] using h
  · rintro ⟨n, h⟩
    exact ⟨n.unpair.1, n.unpair.2, by simpa [haltingPhysUCT, Nat.unpair_pair] using h⟩

/-- Same statement at the packaged **`DiagonalCapable.asr.RT`** axis (defeq with `haltingPhysUCT.RT`). -/
theorem haltingFramework_exists_truth_iff_exists_asr_rt :
    (∃ m : haltingFramework.Model, ∃ r : haltingFramework.Rec, haltingFramework.Truth m r) ↔
      ∃ n : ℕ, haltingFramework_diagonalCapable.asr.RT n := by
  have hRT :
      haltingFramework_diagonalCapable.asr.RT = haltingPhysUCT.RT :=
    rfl
  simpa [hRT] using haltingFramework_exists_truth_iff_exists_physUCT_rt

end Physical
end NemS
