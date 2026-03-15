import ArrowOfTime.Core.RecordFiltration
import ArrowOfTime.Core.Refinement
import ArrowOfTime.Theorems.ArrowRefinement
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false

/-!
# RecordEntropy.Core.HiddenHistoryEntropy

**EPIC_66_SL2 Track 2: Fiber-based hidden-history entropy.**

For RecordFiltration, WorldTypeAt t = Quotient (obsEqAtSetoid t). Each element
is an equivalence class. The **fiber** of a class c at stage t is
{w : World | toWorldTypeAt t w = c}. For Fintype World, each fiber has finite
cardinality.

**Two entropy directions (documented):**
- **Record resolution** (card WorldTypeAt): increases under refinement — more visible
  classes as record grows. See `RecordEntropy.Core.EntropyFinite.recordEntropy`.
- **Fiber-based hidden multiplicity**: fiber sizes DECREASE under refinement — each
  t-class splits into smaller (t+1)-classes. Proved below.
-/

namespace RecordEntropy

universe u v

variable {World : Type u} {Obs : Type v}

open ArrowOfTime ArrowOfTime.RecordFiltration BigOperators

attribute [local instance] Classical.propDecidable

section FiberSize

variable (Filt : RecordFiltration World Obs) (t : ArrowOfTime.Time)

/-- The fiber of a world-type class c at stage t: worlds that map to c. -/
def fiber (c : Filt.WorldTypeAt t) : Set World :=
  {w | Filt.toWorldTypeAt t w = c}

/-- Fiber size: cardinality of the fiber when World is finite.
Equals the number of worlds in the equivalence class represented by c. -/
noncomputable def fiberSize (c : Filt.WorldTypeAt t) [Fintype World] : Nat :=
  (Finset.univ.filter (fun w => Filt.toWorldTypeAt t w = c)).card

theorem fiberSize_eq_card_fiber (c : Filt.WorldTypeAt t) [Fintype World] :
    fiberSize Filt t c = (Finset.univ.filter (fun w => Filt.toWorldTypeAt t w = c)).card :=
  rfl

theorem mem_fiber_iff (c : Filt.WorldTypeAt t) (w : World) :
    w ∈ fiber Filt t c ↔ Filt.toWorldTypeAt t w = c :=
  Iff.rfl

theorem fiberSize_pos_of_mem (c : Filt.WorldTypeAt t) [Fintype World] (w : World)
    (hw : Filt.toWorldTypeAt t w = c) :
    fiberSize Filt t c ≥ 1 := by
  rw [fiberSize_eq_card_fiber]
  exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨w, by simp only [Finset.mem_filter, Finset.mem_univ, hw, and_self]⟩)

theorem fiberSize_pos (c : Filt.WorldTypeAt t) [Fintype World] :
    fiberSize Filt t c ≥ 1 := by
  refine Quotient.inductionOn c (fun repr => ?_)
  exact fiberSize_pos_of_mem Filt t (Quotient.mk _ repr) repr rfl

end FiberSize

section RefinementDecreases

variable (Filt : RecordFiltration World Obs) (t : ArrowOfTime.Time)
variable [Fintype World]

/-- **Fiber size decreases under refinement:** For any (t+1)-class c', its fiber
is a subset of the fiber of its forget-image at t. Thus fiberSize(c') ≤ fiberSize(forget c'). -/
theorem fiberSize_le_under_forget (c' : Filt.WorldTypeAt (t + 1)) :
    fiberSize Filt (t + 1) c' ≤ fiberSize Filt t (Filt.forget t c') := by
  refine Quotient.inductionOn c' (fun w => ?_)
  rw [show Quotient.mk (Filt.obsEqAtSetoid (t + 1)) w = Filt.toWorldTypeAt (t + 1) w from rfl,
      Filt.forget_coherent t w]
  -- fiber of toWorldTypeAt (t+1) w at (t+1) ⊆ fiber of toWorldTypeAt t w at t
  -- For any w' in the (t+1)-fiber of toWorldTypeAt (t+1) w:
  --   toWorldTypeAt (t+1) w' = toWorldTypeAt (t+1) w
  -- Hence ObsEqAt (t+1) w' w, so ObsEqAt t w' w (refinement), so toWorldTypeAt t w' = toWorldTypeAt t w
  -- So the (t+1)-fiber is a subset of the t-fiber
  have hsub : (Finset.univ.filter (fun w' => Filt.toWorldTypeAt (t + 1) w' = Filt.toWorldTypeAt (t + 1) w))
      ⊆ Finset.univ.filter (fun w' => Filt.toWorldTypeAt t w' = Filt.toWorldTypeAt t w) := by
    intro w' hw'
    simp only [Finset.mem_filter] at hw' ⊢
    obtain ⟨_, heq⟩ := hw'
    constructor
    · exact Finset.mem_univ w'
    · have hObs : Filt.ObsEqAt (t + 1) w' w := Quotient.exact heq
      exact Quotient.sound (Filt.refine t (t + 1) w' w (Nat.le_succ t) hObs)
  simp only [fiberSize_eq_card_fiber]
  exact Finset.card_le_card hsub

/-- **Strict decrease when refinement is strict:** When StrictGrowthAt t, there exist
two distinct (t+1)-classes mapping to the same t-class, so each has strictly smaller
fiber than that t-class. -/
theorem fiberSize_lt_under_strict_refinement (hStrict : Filt.StrictGrowthAt t) :
    ∃ c' : Filt.WorldTypeAt (t + 1), fiberSize Filt (t + 1) c' < fiberSize Filt t (Filt.forget t c') := by
  obtain ⟨a, b, hne, heqForget⟩ := Filt.strict_refinement t hStrict
  let c := Filt.forget t a
  have ha : Filt.forget t a = c := rfl
  have hb : Filt.forget t b = c := heqForget.symm
  -- Both a and b have fiber ⊆ fiber of c; their fibers are disjoint and nonempty
  have hle_a := fiberSize_le_under_forget Filt t a
  have hle_b := fiberSize_le_under_forget Filt t b
  -- If both were = fiberSize c, then we'd need two disjoint sets of size fiberSize c
  -- whose union is ⊆ fiber(c) of size fiberSize c — impossible when fiberSize c ≥ 1
  -- and a ≠ b (disjoint nonempty subsets).
  by_contra h
  push_neg at h
  have hle_b' : fiberSize Filt (t + 1) b ≤ fiberSize Filt t c := by rw [← hb]; exact hle_b
  have haeq : fiberSize Filt (t + 1) a = fiberSize Filt t c := Nat.le_antisymm hle_a (h a)
  have hbeq : fiberSize Filt (t + 1) b = fiberSize Filt t c :=
    Nat.le_antisymm hle_b' (congr_arg (fiberSize Filt t) hb ▸ (h b))
  -- Fibers of a and b are disjoint (a ≠ b) and both ⊆ fiber of c
  have hdisj : Disjoint
      (Finset.univ.filter (fun w => Filt.toWorldTypeAt (t + 1) w = a))
      (Finset.univ.filter (fun w => Filt.toWorldTypeAt (t + 1) w = b)) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext w
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ]
    constructor
    · intro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
      exact False.elim (hne (h1.symm.trans h2))
    · intro h
      exact False.elim (Finset.notMem_empty w h)
  have hsubA : (Finset.univ.filter (fun w => Filt.toWorldTypeAt (t + 1) w = a))
      ⊆ Finset.univ.filter (fun w => Filt.toWorldTypeAt t w = c) := by
    intro w hw
    simp only [Finset.mem_filter] at hw ⊢
    constructor
    · exact Finset.mem_univ w
    · rw [← ha, ← Filt.forget_coherent t w, hw.2]
  have hsubB : (Finset.univ.filter (fun w => Filt.toWorldTypeAt (t + 1) w = b))
      ⊆ Finset.univ.filter (fun w => Filt.toWorldTypeAt t w = c) := by
    intro w hw
    simp only [Finset.mem_filter] at hw ⊢
    constructor
    · exact Finset.mem_univ w
    · rw [← hb, ← Filt.forget_coherent t w, hw.2]
  have card_union : (Finset.univ.filter (fun w => Filt.toWorldTypeAt (t + 1) w = a) ∪
      Finset.univ.filter (fun w => Filt.toWorldTypeAt (t + 1) w = b)).card
      = fiberSize Filt (t + 1) a + fiberSize Filt (t + 1) b := by
    rw [Finset.card_union_of_disjoint hdisj, fiberSize_eq_card_fiber, fiberSize_eq_card_fiber]
  have hsub_union : (Finset.univ.filter (fun w => Filt.toWorldTypeAt (t + 1) w = a) ∪
      Finset.univ.filter (fun w => Filt.toWorldTypeAt (t + 1) w = b))
      ⊆ Finset.univ.filter (fun w => Filt.toWorldTypeAt t w = c) := by
    intro w hw
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ] at hw ⊢
    constructor
    · trivial
    · cases hw with
      | inl h => rw [← ha, ← Filt.forget_coherent t w, h.2]
      | inr h => rw [← hb, ← Filt.forget_coherent t w, h.2]
  have hcard_le : fiberSize Filt (t + 1) a + fiberSize Filt (t + 1) b ≤ fiberSize Filt t c := by
    rw [← card_union]
    trans (Finset.univ.filter (fun w => Filt.toWorldTypeAt t w = c)).card
    · exact Finset.card_le_card hsub_union
    · rw [fiberSize_eq_card_fiber]
  rw [haeq, hbeq] at hcard_le
  have hpos : fiberSize Filt t c ≥ 1 := fiberSize_pos Filt t c
  omega

end RefinementDecreases

section HiddenHistoryEntropy

/-- **Hidden-history entropy (max fiber):** The maximum fiber size at stage t.
Decreases under refinement (per fiberSize_le_under_forget). -/
noncomputable def maxFiberSize (Filt : RecordFiltration World Obs) (t : ArrowOfTime.Time)
    [Fintype World] [Fintype (Filt.WorldTypeAt t)] : Nat :=
  Finset.univ.sup (fun c => fiberSize Filt t c)

/-- **Sum of fiber sizes equals world count:** Fibers partition World (equivalence classes
of obsEqAtSetoid t), so ∑_c fiberSize(c) = |World|. -/
theorem sum_fiberSize_eq_card (Filt : RecordFiltration World Obs) (t : ArrowOfTime.Time)
    [Fintype World] [Fintype (Filt.WorldTypeAt t)] :
    ∑ c ∈ Finset.univ, fiberSize Filt t c = Fintype.card World := by
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
    (fun w _ => Finset.mem_univ (Filt.toWorldTypeAt t w))]
  apply Finset.sum_congr rfl
  intro c _
  rw [fiberSize_eq_card_fiber]

end HiddenHistoryEntropy

end RecordEntropy
