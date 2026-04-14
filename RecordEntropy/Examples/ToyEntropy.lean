import RecordEntropy.Core.EntropyFinite
import RecordEntropy.Core.HiddenHistoryEntropy
import RecordEntropy.Theorems.Monotonicity
import RecordEntropy.Theorems.NoncomputabilityBarrier
import ArrowOfTime.Examples.Toy
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false

/-!
# RecordEntropy.Examples.ToyEntropy

**Paper 42: Toy witness for record entropy.**

Two-bit filtration (ArrowOfTime.Toy): Fintype instances for WorldTypeAt 0 and 1,
monotonicity, strict growth at t=0, and barrier predicate nontrivial.

**Toy fiber structure (fiber-based hidden entropy track)** — at t=0: 2 classes of size 2 each;
at t=1: 4 classes of size 1 each. Fiber sizes decrease under refinement.
-/

namespace RecordEntropy

open ArrowOfTime
open ArrowOfTime.RecordFiltration
open ArrowOfTime.Toy

attribute [local instance] Classical.propDecidable

/-- ToyWorld = Bool × Bool is finite. -/
instance toyWorldFintype : Fintype ToyWorld :=
  show Fintype (Bool × Bool) from inferInstance

/-- At time 0, Toy quotient has 2 world-types (first bit distinguishes). -/
noncomputable instance filtWorldTypeAt0Fintype : Fintype (filt.WorldTypeAt 0) :=
  Quotient.fintype (filt.obsEqAtSetoid 0)

/-- At time 1, Toy quotient has 4 world-types (both bits visible). -/
noncomputable instance filtWorldTypeAt1Fintype : Fintype (filt.WorldTypeAt 1) :=
  Quotient.fintype (filt.obsEqAtSetoid 1)

/-- WorldTypeAt (0+1) = WorldTypeAt 1 for Toy. -/
noncomputable instance filtWorldTypeAt0Plus1Fintype : Fintype (filt.WorldTypeAt (0 + 1)) :=
  filtWorldTypeAt1Fintype

/-- Record entropy is monotone for Toy at t=0. -/
theorem toy_entropy_monotone : recordEntropy filt 1 ≥ recordEntropy filt 0 :=
  recordEntropy_monotone filt 0

/-- Record entropy is strictly increasing for Toy at t=0. -/
theorem toy_entropy_strict : recordEntropy filt 1 > recordEntropy filt 0 :=
  recordEntropy_strict filt 0 toy_strict_growth

/-- The entropy claim for Toy at t=0 is nontrivial. -/
theorem toy_entropy_claim_nontrivial : SelectorStrength.Nontrivial (entropyClaim filt 0) :=
  entropyClaim_nontrivial filt 0

/-- Barrier applies to Toy entropy claim at t=0 under hFP and anti-closure. -/
theorem toy_no_total_decider_entropy
    (Sbool : SelectorStrength.Strength Nat Bool) (Sα : SelectorStrength.Strength Nat Nat)
    (hAnti : SelectorStrength.AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : Nat → Nat, Sα F → ∃ d : Nat, d = F d) :
    ¬ SelectorStrength.DecidableAt Sbool (entropyClaim filt 0) :=
  no_total_decider_entropy filt 0 Sbool Sα hAnti hFP

-- ========== Fiber-based hidden-history entropy (fiber-based hidden entropy track) ==========

/-- At t=0, each class has fiber size 2 (two worlds per class: same first bit). -/
theorem toy_fiberSize_at_0 (c : filt.WorldTypeAt 0) :
    fiberSize filt 0 c = 2 := by
  refine Quotient.inductionOn c (fun repr => ?_)
  have heq_filter : (Finset.univ.filter (fun w => filt.toWorldTypeAt 0 w = filt.toWorldTypeAt 0 repr)) =
      Finset.univ.filter (fun w : ToyWorld => w.1 = repr.1) := by
    ext w
    simp only [filt_Holds, filt_Visible, holds, visible, Finset.mem_filter, Finset.mem_univ]
    constructor
    · intro ⟨_, heq⟩
      have this := Quotient.exact heq
      constructor
      · trivial
      · have h := this false trivial
        simp only [filt_Holds, holds] at h
        cases hw1 : w.1 <;> cases hr1 : repr.1 <;> simp_all
    · intro hw
      constructor
      · trivial
      · exact Quotient.sound (fun o vo => by
          cases o <;> simp only [filt_Holds, holds, visible] at vo ⊢
          · -- goal: w.1 = true ↔ repr.1 = true; hw.2 : w.1 = repr.1
            rw [hw.2]
          · exact absurd vo (by simp [visible]))
  rw [fiberSize_eq_card_fiber, show Quotient.mk (filt.obsEqAtSetoid 0) repr = filt.toWorldTypeAt 0 repr from rfl,
      heq_filter]
  -- Finset.univ for Bool×Bool filtered by w.1 = repr.1: exactly (repr.1, false) and (repr.1, true)
  have : (Finset.univ : Finset ToyWorld).filter (fun w => w.1 = repr.1) = {(repr.1, false), (repr.1, true)} := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      fin_cases b
      · -- b = true (fin_cases «0» = true for Bool)
        -- goal: (a, true) ∈ {(repr.1, false), (repr.1, true)}
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (by rw [h])))
      · -- b = false
        exact Finset.mem_insert.mpr (Or.inl (by rw [h]))
    · intro h
      rcases Finset.mem_insert.mp h with h1 | h2
      · -- h1 : (a, b) = (repr.1, false); Prod.ext_iff.mp h1 : a = repr.1 ∧ b = false
        exact (Prod.ext_iff.mp h1).1
      · exact (Prod.ext_iff.mp (Finset.mem_singleton.mp h2)).1

  rw [this]
  -- {(repr.1, false), (repr.1, true)}.card = 2
  have hne : (repr.1, false) ∉ ({(repr.1, true)} : Finset ToyWorld) := by
    intro h
    have := Finset.mem_singleton.mp h
    exact Bool.false_ne_true (Prod.ext_iff.mp this).2
  -- The set {(repr.1, false), (repr.1, true)} has 2 elements since false ≠ true
  have hne2 : (repr.1, false) ≠ (repr.1, true) := by
    intro h; exact Bool.false_ne_true (Prod.ext_iff.mp h).2
  exact Finset.card_pair hne2

/-- At t=1, each class has fiber size 1 (both bits visible, all worlds distinct). -/
theorem toy_fiberSize_at_1 (c : filt.WorldTypeAt 1) :
    fiberSize filt 1 c = 1 := by
  refine Quotient.inductionOn c (fun repr => ?_)
  have hsub : (Finset.univ.filter (fun w => filt.toWorldTypeAt 1 w = filt.toWorldTypeAt 1 repr)) ⊆ {repr} := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton] at hw ⊢
    have hObs := Quotient.exact hw.2
    unfold ToyWorld; ext
    · have h1 := hObs false trivial
      simp only [filt_Holds, holds] at h1
      -- h1 : w.1 = true ↔ repr.1 = true  (Bool coercion)
      -- cases false.true: h1 : false = true ↔ true = true; h1 means repr.1 = true but w.1 = false
      cases hw1 : w.1 <;> cases hr1 : repr.1 <;> simp_all
    · have h2 := hObs true (Nat.le_refl 1)
      simp only [filt_Holds, holds] at h2
      cases hw2 : w.2 <;> cases hr2 : repr.2 <;> simp_all
  have hmem : repr ∈ Finset.univ.filter (fun w => filt.toWorldTypeAt 1 w = filt.toWorldTypeAt 1 repr) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have : (Finset.univ.filter (fun w => filt.toWorldTypeAt 1 w = filt.toWorldTypeAt 1 repr)).card = 1 := by
    rw [Finset.eq_singleton_iff_unique_mem.2 ⟨hmem, fun x hx => Finset.mem_singleton.1 (hsub hx)⟩,
        Finset.card_singleton repr]
  rw [fiberSize_eq_card_fiber, show Quotient.mk (filt.obsEqAtSetoid 1) repr = filt.toWorldTypeAt 1 repr from rfl,
      this]

/-- Fiber size decreases under refinement for Toy at t=0. -/
theorem toy_fiberSize_le_under_forget (c' : filt.WorldTypeAt 1) :
    fiberSize filt 1 c' ≤ fiberSize filt 0 (filt.forget 0 c') :=
  fiberSize_le_under_forget filt 0 c'

/-- Strict decrease: at t=0 there exists a (t+1)-class with strictly smaller fiber than its forget-image. -/
theorem toy_fiberSize_lt_under_strict :
    ∃ c' : filt.WorldTypeAt 1, fiberSize filt 1 c' < fiberSize filt 0 (filt.forget 0 c') :=
  fiberSize_lt_under_strict_refinement filt 0 toy_strict_growth

end RecordEntropy
