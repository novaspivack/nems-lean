import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Closure.Core.ObsSemantics
import Closure.Core.Selector
import Closure.Core.Effective
import Closure.Core.Canonicalization
import Closure.Theorems.BoundedSelector

/-!
# Closure.Examples.FintypeWorld

**Toy nailed instance:** when `World` is finite and observational equivalence is
decidable, we build an `EffectiveSemantics` and a `BoundedCover`, then apply the
bounded-search selector from `Closure.Theorems.BoundedSelector`.

This demonstrates that the Closure toolkit is non-empty: the abstract
"internal symmetry-breaking" path has a concrete constructive instance.
-/

set_option autoImplicit false

namespace Closure

namespace Examples

universe u v

variable {World : Type u} {Obs : Type v}

section FintypeWorld

variable (S : ObsSemantics World Obs) [Fintype World] [Nonempty World] [DecidableRel S.ObsEquiv]

/-- Enumerate worlds by cycling through the Fintype equivalence to `Fin card`.
    Noncomputable (Fintype.equivFin uses a choice of ordering). -/
noncomputable def enumOfFintype (n : Nat) : World :=
  (Fintype.equivFin World).symm ⟨n % Fintype.card World, Nat.mod_lt n (Fintype.card_pos (α := World))⟩

theorem enumOfFintype_surj (w : World) : ∃ n, enumOfFintype n = w := by
  use (Fintype.equivFin World w).val
  simp only [enumOfFintype]
  have heq : ⟨(Fintype.equivFin World w).val % Fintype.card World, Nat.mod_lt (Fintype.equivFin World w).val (Fintype.card_pos (α := World))⟩ = Fintype.equivFin World w :=
    Fin.ext (Nat.mod_eq_of_lt (Fintype.equivFin World w).2)
  rw [heq, (Fintype.equivFin World).symm_apply_apply w]

/-- Effective semantics induced by Fintype World: enum lists all worlds (cycling). -/
noncomputable def effectiveSemanticsOfFintype : EffectiveSemantics World Obs where
  semantics := S
  enum := enumOfFintype
  surj := enumOfFintype_surj
  decObsEquiv := inferInstance

/-- Every world appears at an index < Fintype.card World. -/
theorem enumOfFintype_lt_card (w : World) :
    ∃ n : Nat, n < Fintype.card World ∧ enumOfFintype n = w := by
  have card_pos : 0 < Fintype.card World := Fintype.card_pos (α := World)
  obtain ⟨k, hk⟩ := enumOfFintype_surj w
  refine ⟨k % Fintype.card World, Nat.mod_lt k card_pos, ?_⟩
  rw [← hk]; simp only [enumOfFintype]; congr 1; exact Fin.ext (Nat.mod_mod k (Fintype.card World))

/-- Bounded cover: every world-type has a representative in the first `card` positions. -/
def boundedCoverOfFintype : BoundedCover (effectiveSemanticsOfFintype S) where
  cover := Fintype.card World
  cover_spec t := by
    obtain ⟨w, hw⟩ := Quotient.exists_rep (s := S.obsEquivSetoid) t
    obtain ⟨n, hn, heq⟩ := enumOfFintype_lt_card w
    exact ⟨n, hn, (congr_arg S.toWorldType heq).trans hw⟩

/-- With a canonicalization, we get a selector (classical: uses Choice from bounded cover).
    For a total bounded-search selector use `boundedSelectorAsSelector` when
    `[DecidableEq S.WorldType]` is available (e.g. from decidable ObsEquiv + quotient). -/
noncomputable def selectorOfFintypeWorld (C : Canonicalization S) :
    Selector (effectiveSemanticsOfFintype S).semantics :=
  Classical.choice (nonempty_selector_of_bounded_cover (effectiveSemanticsOfFintype S) (boundedCoverOfFintype S) C)

theorem selectorOfFintypeWorld_section (C : Canonicalization S) (t : S.WorldType) :
    S.toWorldType ((selectorOfFintypeWorld S C).sel t) = t :=
  (selectorOfFintypeWorld S C).sec t

end FintypeWorld

end Examples

end Closure
