import SelfReference.Core.Interface

/-!
# SelfReference.Minimality.UnitypedNatReprObstruction

## Unityped `ℕ` + `SRI₀′` cannot have `Equiv = Eq`

This is the standard Lawvere/Cantor diagonal for a **point-surjective** `run ∘ repr` at equality:
if `repr_spec` used **propositional** equality of outputs, then `ℕ → ℕ` has too many functions to
be represented by a single `ℕ` of codes.

For **Paper 51** / `barrier_hypotheses_from_reflection`, the mathematical tension is:

- **Reflection + `allRepresentable`** needs a **full** unityped `SRI₀′` on `F.Code` (every
  `F' : Code → Code` represented).
- **`EncodedNontrivial`** needs **at least two** `CodeEquiv`-classes (see
  `SemanticSelfDescription.false_of_encodedNontrivial_indiscrete_CodeEquiv`).
- If `CodeEquiv` is **discrete** (`↔` `Eq` on `ℕ`), **this module** rules out the `SRI₀′` side.
- If `CodeEquiv` is **coarser** than `Eq` (e.g. Gödel `ProvBic`, Kleene **extensional** `ExtEq` on
  indices), **diagonal at `Eq` does not apply verbatim** — but then you need a **concrete**
  arithmetic/program model supplying coherent `run`, `repr`, **and** a **`RealizedTrue` / `decode`**
  story compatible with **both** that equivalence **and** **encoded nontriviality**.

Abstract `GodelSystem` with *universal* true `ProvBic` supports `toSRI0'` trivially, but is
incompatible with **`EncodedNontrivial`** once `CodeEquiv` is aligned with `ProvBic`.
-/

set_option autoImplicit false

namespace SelfReference
namespace Minimality

/-- **Diagonal obstruction:** no `SRI₀′` on `ℕ` can have `Equiv` **coincide** with `Eq`. -/
theorem not_nonempty_sri0'_nat_equiv_eq :
    ¬ Nonempty (Subtype fun S : SRI0' ℕ ℕ => ∀ x y, S.Equiv x y ↔ x = y) := by
  rintro ⟨S, hEq⟩
  let G : ℕ → ℕ := fun c => Nat.succ (S.run c c)
  let e : ℕ := S.repr G
  have hspec := S.repr_spec G e
  have hEq' := (hEq _ _).1 hspec
  dsimp [G] at hEq'
  exact Nat.succ_ne_self _ hEq'.symm

end Minimality
end SelfReference
