-- k-role lower bound (Paper 40)
import InstitutionalEpistemics.Core.Roles
import InstitutionalEpistemics.Core.ThreatModel
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

variable (Instance : Type*) [Fintype Instance] (k : ℕ)

namespace InstitutionalEpistemics

/-- A k-partition of Instance: k disjoint nonempty sets whose union is all instances. -/
structure KPartition where
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
  simp only [Nat.lt_iff_not_le, not_le] at hk
  have card_roles : Fintype.card (Role roles) = roles := by rw [Role]; exact Fintype.card_fin
  have card_k : Fintype.card (Fin k) = k := Fintype.card_fin
  have : Fintype.card (Role roles) < Fintype.card (Fin k) := by rw [card_roles, card_k]; exact hk
  -- Pigeonhole: ≥k parts need coverage, each role covers only one part (hone) ⇒ need ≥k roles.
  sorry
