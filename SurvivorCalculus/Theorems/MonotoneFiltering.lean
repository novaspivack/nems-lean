import SurvivorCalculus.Core.Cascade
import Sieve.Theorems.Residual
import Mathlib.Data.List.Infix

/-!
# SurvivorCalculus.Theorems.MonotoneFiltering

Monotone cascade: R_{k+1} ⊆ R_k.
-/

set_option autoImplicit false

namespace SurvivorCalculus

variable {α : Type _}

/-- **Monotone cascade theorem:** Adding constraints yields residual inclusion.
If x satisfies the first (k+1) constraints, it satisfies the first k. -/
theorem residual_inclusion (cs : Cascade α) (k : ℕ) (x : α)
    (h : ResidualClass α cs (k + 1) x) :
    ResidualClass α cs k x := by
  unfold ResidualClass at *
  have hsub : (cs.take k).Sublist (cs.take (k + 1)) := by
    have hpre : cs.take k <+: cs.take (k + 1) := List.take_isPrefix_take.mpr (Or.inl (Nat.le_succ _))
    exact hpre.sublist
  exact Sieve.residual_mono (cs.take k) (cs.take (k + 1)) x hsub h

end SurvivorCalculus
