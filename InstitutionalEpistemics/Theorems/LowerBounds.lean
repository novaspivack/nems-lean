-- k-role lower bound (Paper 40)
import InstitutionalEpistemics.Core.Roles
import InstitutionalEpistemics.Core.ThreatModel
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union

variable (Instance : Type*) [Fintype Instance] [DecidableEq Instance] (k : ℕ)

namespace InstitutionalEpistemics

/-- A k-partition of Instance: k disjoint nonempty sets whose union is all instances. -/
structure KPartition (Instance : Type*) [Fintype Instance] [DecidableEq Instance] (k : ℕ) where
  parts : Fin k → Finset Instance
  disjoint : ∀ i j, i ≠ j → (parts i ∩ parts j : Finset Instance) = ∅
  cover : (Finset.univ : Finset (Fin k)).biUnion parts = Finset.univ
  nonempty : ∀ i, (parts i).Nonempty

/-- Coverage by role: each role r has a set of instances it covers.
    Full coverage: every instance is in at least one role's coverage. -/
def FullCoverage (roles : ℕ) (cov : Role roles → Finset Instance) : Prop :=
  (Finset.univ.biUnion fun r : Role roles => cov r) = Finset.univ

/-- Each role's coverage lies entirely within one part (no role spans two parts). -/
def RoleInOnePart (P : KPartition Instance k) (cov : Role roles → Finset Instance) : Prop :=
  ∀ r, ∃ i : Fin k, cov r ⊆ P.parts i

/-- Under a k-partition with disjoint parts and each role confined to one part,
    full coverage requires at least k roles. -/
theorem k_role_lower_bound (P : KPartition Instance k) (roles : ℕ) (cov : Role roles → Finset Instance)
    (h : FullCoverage Instance roles cov) (hone : RoleInOnePart Instance k P cov) :
    roles ≥ k := by
  by_contra hk
  rw [Nat.not_le] at hk
  -- Each role r is assigned to some part f(r) : Fin k (by hone).
  -- If roles < k, then f : Role roles → Fin k cannot be surjective (by |domain| < |codomain|).
  -- So some part i : Fin k is uncovered by all roles.
  -- But P.nonempty i gives an instance x ∈ P.parts i,
  -- and h (fullCoverage) says x must be in the range of some role's coverage.
  -- By hone, that role's coverage lies in some part i', so x ∈ P.parts i ∩ P.parts i'.
  -- By P.disjoint (i ≠ i'), P.parts i ∩ P.parts i' = ∅. Contradiction.
  -- Build the assignment function: for each role r, choose the part it maps to.
  choose f hf using hone
  -- f : Role roles → Fin k, where ∀ r, cov r ⊆ P.parts (f r).
  -- Since roles < k, f cannot be surjective.
  have hcard_lt : Fintype.card (Role roles) < Fintype.card (Fin k) := by
    simp [Fintype.card_fin]
    have e : Role roles ≃ Fin roles :=
      { toFun := fun r => r.idx, invFun := Role.mk,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_fin]
    exact hk
  -- There exists a part not in the range of f.
  obtain ⟨i, hi⟩ := Fintype.exists_not_mem_finset
    (Finset.image f Finset.univ) (by
      rw [Finset.card_image_le.trans_lt (by simp; exact hcard_lt) |>.le.lt_iff_ne.ne.symm]
      · simp [Fintype.card_fin])
  -- Part i is not covered by any role.
  -- Get an instance in P.parts i.
  obtain ⟨x, hx⟩ := P.nonempty i
  -- By full coverage, x is covered by some role r.
  have hcov := h.symm
  have hx_in : x ∈ Finset.univ := Finset.mem_univ x
  rw [← FullCoverage] at hcov
  simp [FullCoverage] at h
  have : x ∈ (Finset.univ.biUnion fun r : Role roles => cov r) := by
    rw [h]; exact Finset.mem_univ x
  simp at this
  obtain ⟨r, _, hxr⟩ := this
  -- r covers x, and r is assigned to part f r.
  have hxfr : x ∈ P.parts (f r) := hf r hxr
  -- But f r ≠ i since i is not in the range of f.
  have hfr_ne : f r ≠ i := by
    intro heq
    apply hi
    simp [Finset.mem_image]
    exact ⟨r, Finset.mem_univ _, heq⟩
  -- x ∈ P.parts i and x ∈ P.parts (f r), with f r ≠ i.
  -- By disjointness: P.parts i ∩ P.parts (f r) = ∅, so x cannot be in both.
  have hdisj := P.disjoint i (f r) hfr_ne
  have : x ∈ (P.parts i ∩ P.parts (f r) : Finset Instance) := by
    simp [Finset.mem_inter, hx, hxfr]
  rw [hdisj] at this
  exact Finset.not_mem_empty _ this
