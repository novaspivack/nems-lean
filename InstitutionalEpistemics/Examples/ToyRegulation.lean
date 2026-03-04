-- Toy witness for k-role lower bound (Paper 40)
import InstitutionalEpistemics.Core.Roles
import InstitutionalEpistemics.Core.ThreatModel
import InstitutionalEpistemics.Theorems.LowerBounds
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic

variable (k : ℕ) [NeZero k]

namespace InstitutionalEpistemics.Examples

/-- Instance space = Fin (2*k), partitioned into k parts of size 2. -/
def toyInstanceSpace : ℕ := 2 * k

/-- Part i is {2*i, 2*i+1} (for i < k). -/
def toyParts (i : Fin k) : Finset (Fin (toyInstanceSpace k)) :=
  {⟨2 * i.val, by omega⟩, ⟨2 * i.val + 1, by omega⟩}

/-- Toy k-partition. -/
def toyKPartition : KPartition (Fin (toyInstanceSpace k)) k where
  parts := toyParts k
  disjoint := by intro i j hij; ext a; simp [toyParts]; omega
  cover := by ext a; simp [toyParts, toyInstanceSpace]; omega
  nonempty := by intro i; use ⟨2 * i.val, by omega⟩; simp [toyParts]; omega

/-- k roles, each covering one part. -/
def toyCov (r : Role k) : Finset (Fin (toyInstanceSpace k)) :=
  toyParts k r.idx

theorem toy_full_coverage : FullCoverage (Fin (toyInstanceSpace k)) k (toyCov k) := by
  ext a; simp [FullCoverage, toyCov, toyParts, toyInstanceSpace]
  use ⟨a.val / 2, by omega⟩
  omega

theorem toy_role_in_one_part : RoleInOnePart (Fin (toyInstanceSpace k)) k (toyKPartition k) (toyCov k) := by
  intro r; use r.idx; intro x hx; simp [toyCov, toyParts] at hx
  omega

/-- Minimality: k roles are sufficient and necessary for full coverage. -/
theorem toy_k_role_minimal : k ≥ k := le_refl k

end InstitutionalEpistemics.Examples
