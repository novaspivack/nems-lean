import SelfReference.Core.Interface

/-!
# Reflection.Core.SRI_R

**Restricted Self-Reference Interface (SRI_R)**

Parameterize representability by a class `R : (Code → Obj) → Prop`.
`repr` is defined only for transformers `F` with `R F`, satisfying `repr_spec`.

This yields a resource theory of reflection: systems may only internalize
transformers in a restricted class. The **Diagonal Closure Theorem** says:
when `R` is closed under the diagonalization template
`F ↦ (c ↦ F(quote(run c c)))`, every `F ∈ R` has a mixed fixed point.

## Key definitions

- `SRI_R Obj Code R` : structure with Equiv, quote, run, and restricted repr
- `DiagClosed R` : R is closed under the diagonalization template
-/

set_option autoImplicit false

namespace Reflection

universe u v

/-! ## Restricted SRI -/

/-- **Restricted Self-Reference Interface (SRI_R).**

Represents only transformers in class `R`. For `F` with `R F`, we have
`repr F hF : Code` such that `run (repr F hF) c ≃ F c` for all `c`. -/
class SRI_R (Obj : Type u) (Code : Type v) (R : (Code → Obj) → Prop) where
  Equiv       : Obj → Obj → Prop
  equiv_refl  : ∀ x, Equiv x x
  equiv_symm  : ∀ {x y}, Equiv x y → Equiv y x
  equiv_trans : ∀ {x y z}, Equiv x y → Equiv y z → Equiv x z
  quote       : Obj → Code
  run         : Code → Code → Obj
  repr        : (F : Code → Obj) → R F → Code
  repr_spec   : ∀ (F : Code → Obj) (hF : R F) (c : Code),
      Equiv (run (repr F hF) c) (F c)

/-! ## Diagonal closure -/

/-- **Diagonally closed**: `R` is closed under the diagonalization template.

If `F ∈ R`, then `G_F` defined by `G_F(c) := F(quote(run c c))` is also in `R`.

This is the key condition for the Diagonal Closure Theorem: when `R` is
diagonally closed, every `F ∈ R` has a mixed fixed point. -/
def DiagClosed {Obj : Type u} {Code : Type v} (R : (Code → Obj) → Prop)
    [S : SRI_R Obj Code R] : Prop :=
  ∀ F, R F → R (fun c => F (S.quote (S.run c c)))

namespace SRI_R

variable {Obj : Type u} {Code : Type v} {R : (Code → Obj) → Prop}
  [S : SRI_R Obj Code R]

theorem equiv_is_equivalence : Equivalence (SRI_R.Equiv (Obj := Obj) (Code := Code) (R := R)) :=
  ⟨SRI_R.equiv_refl, SRI_R.equiv_symm, SRI_R.equiv_trans⟩

def equivSetoid : Setoid Obj where
  r     := SRI_R.Equiv (Obj := Obj) (Code := Code) (R := R)
  iseqv := equiv_is_equivalence

end SRI_R

/-! ## Bridge: full SRI₀′ induces SRI_R with R = ⊤ -/

/-- The predicate "all transformers are representable" (Trivially true). -/
def allRepresentable {Obj : Type u} {Code : Type v} (_ : Code → Obj) : Prop := True

/-- Every SRI₀′ induces SRI_R with R = allRepresentable (i.e. all F). -/
instance sri0'_to_sri_r (Obj : Type u) (Code : Type v) [S : SelfReference.SRI0' Obj Code] :
    SRI_R Obj Code (allRepresentable (Obj := Obj) (Code := Code)) where
  Equiv       := S.Equiv
  equiv_refl  := S.equiv_refl
  equiv_symm  := S.equiv_symm
  equiv_trans := S.equiv_trans
  quote       := S.quote
  run         := S.run
  repr F _    := S.repr F
  repr_spec F _ c := S.repr_spec F c

/-- `allRepresentable` is diagonally closed (trivially: it contains everything). -/
instance diagClosed_allRepresentable (Obj : Type u) (Code : Type v)
    [SRI_R Obj Code (allRepresentable (Obj := Obj) (Code := Code))] :
    DiagClosed (allRepresentable (Obj := Obj) (Code := Code)) :=
  fun _ _ => trivial

end Reflection
