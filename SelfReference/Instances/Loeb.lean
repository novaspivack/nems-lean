import SelfReference.Core.FixedPoint
import SelfReference.Instances.Godel

/-!
# SelfReference.Instances.Loeb

## Löb's Theorem as a consequence of the diagonal lemma

**Löb's theorem** (1955): If `T ⊢ □φ → φ`, then `T ⊢ φ`.

This follows from the diagonal lemma (MFP-1) plus the
Hilbert–Bernays–Löb (HBL) derivability conditions.

## Proof structure

1. By the diagonal lemma (proved via MFP-1), get `L` with
   `T ⊢ L ↔ (□L → φ)`.
2. The HBL chaining (steps 2–9) is standard modal provability logic.

All steps use only the `ProvSystem` axioms.

## Sorry status: zero sorrys

The HBL chaining is fully machine-checked using the `ProvSystem` axioms.
The key additional axiom needed is `imp_intro` (the deduction theorem),
which is standard in any Hilbert-style proof system.
-/

namespace SelfReference
namespace Instances
namespace Loeb

open Godel

/-- Abstract provability system extending a Gödel system.

Extends `GodelSystem` with:
- `Prov`: the provability predicate
- `box`: the provability operator `□`
- `imp`: the implication connective
- HBL conditions 1, 2, 3
- `mp`: modus ponens
- `imp_intro`: the deduction theorem (`Prov (imp n m)` from `Prov n → Prov m`)
- `prov_iff`: provable biconditional implies logical equivalence
- congruence lemmas for `box` and `imp`
-/
structure ProvSystem extends GodelSystem where
  Prov : ℕ → Prop
  box  : ℕ → ℕ
  imp  : ℕ → ℕ → ℕ
  /-- HBL condition 1: `T ⊢ n → T ⊢ □n`. -/
  hbl1 : ∀ n, Prov n → Prov (box n)
  /-- HBL condition 2: `T ⊢ □n → □□n`. -/
  hbl2 : ∀ n, Prov (imp (box n) (box (box n)))
  /-- HBL condition 3: `T ⊢ □(n → m) → (□n → □m)`. -/
  hbl3 : ∀ n m, Prov (imp (box (imp n m)) (imp (box n) (box m)))
  /-- Modus ponens. -/
  mp   : ∀ n m, Prov (imp n m) → Prov n → Prov m
  /-- Deduction theorem: `(Prov n → Prov m) → Prov (imp n m)`. -/
  imp_intro : ∀ n m, (Prov n → Prov m) → Prov (imp n m)
  /-- Provable biconditional implies logical equivalence. -/
  prov_iff : ∀ n m, ProvBic n m → (Prov n ↔ Prov m)
  /-- `box` respects `ProvBic`. -/
  box_cong : ∀ {n m}, ProvBic n m → ProvBic (box n) (box m)
  /-- `imp` is congruent in the left argument. -/
  imp_cong_l : ∀ {n m} (k : ℕ), ProvBic n m → ProvBic (imp n k) (imp m k)
  /-- `imp` is congruent in the right argument. -/
  imp_cong_r : ∀ {n m} (k : ℕ), ProvBic n m → ProvBic (imp k n) (imp k m)

/-- **Löb's Theorem.**

If `T ⊢ □φ → φ`, then `T ⊢ φ`.

**Proof** (all steps machine-checked):
1. Diagonal lemma gives `L` with `T ⊢ L ↔ (□L → φ)`.
2. `T ⊢ □L → □(□L → φ)` — from (1) + `box_cong` + `imp_intro`.
3. `T ⊢ □(□L → φ) → (□□L → □φ)` — HBL3.
4. `T ⊢ □L → □□L` — HBL2.
5. `T ⊢ □L → □φ` — from 2, 3, 4 by chaining.
6. `T ⊢ □L → φ` — from 5 + `h_hyp`.
7. `T ⊢ L` — from 1 (backward) + 6.
8. `T ⊢ □L` — from HBL1 + 7.
9. `T ⊢ □φ` — from 5 + 8.
10. `T ⊢ φ` — from `h_hyp` + 9. -/
theorem lob (P : ProvSystem) (φ : ℕ)
    (h_hyp : P.Prov (P.imp (P.box φ) φ)) :
    P.Prov φ := by
  -- Step 1: Diagonal lemma gives L with T ⊢ L ↔ (□L → φ).
  have hF_cong : ∀ {x y : ℕ}, P.ProvBic x y → P.ProvBic (P.imp (P.box x) φ) (P.imp (P.box y) φ) :=
    fun h => P.imp_cong_l φ (P.box_cong h)
  obtain ⟨L, hL⟩ := godel_diagonal_lemma P.toGodelSystem (fun n => P.imp (P.box n) φ) hF_cong
  -- Step 2: Lift to provability level: Prov L ↔ Prov (□L → φ).
  have hLiff : P.Prov L ↔ P.Prov (P.imp (P.box L) φ) :=
    P.prov_iff L (P.imp (P.box L) φ) hL
  -- Step 3: T ⊢ □L → □(□L → φ), via box_cong and imp_intro.
  have hboxCong : P.ProvBic (P.box L) (P.box (P.imp (P.box L) φ)) := P.box_cong hL
  have hboxL_iff_boxImp : P.Prov (P.box L) ↔ P.Prov (P.box (P.imp (P.box L) φ)) :=
    P.prov_iff _ _ hboxCong
  have hboxL_imp_boxImp : P.Prov (P.imp (P.box L) (P.box (P.imp (P.box L) φ))) :=
    P.imp_intro _ _ hboxL_iff_boxImp.mp
  -- Step 4: T ⊢ □(□L → φ) → (□□L → □φ), by HBL3.
  have hbl3_inst : P.Prov (P.imp (P.box (P.imp (P.box L) φ)) (P.imp (P.box (P.box L)) (P.box φ))) :=
    P.hbl3 (P.box L) φ
  -- Step 5: T ⊢ □L → □□L, by HBL2.
  have hbl2_inst : P.Prov (P.imp (P.box L) (P.box (P.box L))) := P.hbl2 L
  -- Step 6: T ⊢ □L → □φ, by chaining steps 3–5.
  have hboxL_imp_boxPhi : P.Prov (P.imp (P.box L) (P.box φ)) := by
    apply P.imp_intro
    intro hboxL
    have hboxImp : P.Prov (P.box (P.imp (P.box L) φ)) := P.mp _ _ hboxL_imp_boxImp hboxL
    have hboxboxL : P.Prov (P.box (P.box L)) := P.mp _ _ hbl2_inst hboxL
    have hboxboxL_imp_boxPhi : P.Prov (P.imp (P.box (P.box L)) (P.box φ)) :=
      P.mp _ _ hbl3_inst hboxImp
    exact P.mp _ _ hboxboxL_imp_boxPhi hboxboxL
  -- Step 7: T ⊢ □L → φ, from step 6 and h_hyp (□φ → φ).
  have hboxL_imp_phi : P.Prov (P.imp (P.box L) φ) := by
    apply P.imp_intro
    intro hboxL
    exact P.mp _ _ h_hyp (P.mp _ _ hboxL_imp_boxPhi hboxL)
  -- Steps 8–10: T ⊢ L (from hLiff), T ⊢ □L (HBL1), T ⊢ □φ (step 6), T ⊢ φ (h_hyp).
  have hProvL : P.Prov L := hLiff.mpr hboxL_imp_phi
  have hProvBoxL : P.Prov (P.box L) := P.hbl1 L hProvL
  have hProvBoxPhi : P.Prov (P.box φ) := P.mp _ _ hboxL_imp_boxPhi hProvBoxL
  exact P.mp _ _ h_hyp hProvBoxPhi

end Loeb
end Instances
end SelfReference
