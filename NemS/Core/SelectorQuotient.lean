import NemS.Core.Selectors
import Mathlib.Logic.Equiv.Basic

/-!
# NemS.Core.SelectorQuotient

## Selectors as quotient splittings

Every selector on `F.Model` is in canonical bijection with the type of
sections of the quotient map `toWorldType : F.Model → Quotient(obsEqSetoid F)`.

This file proves the **selector–quotient splitting equivalence**:

1. `selector_quotient_splitting` — every selector factors through a section
   of `toWorldType` (existential form with factorization).
2. `selector_equiv_section` — the section is unique (∃! form; forward direction
   of the bijection).
3. `quotientSectionToSelector` — constructive converse: a section induces a
   valid `Selector`.
4. `section_defines_selector_general` — existential form of the converse.
5. `selectorSectionEquiv` — the full `Equiv` packaging the bijection.

**Key consequence:** a selector is not merely a canonical-representative map
that happens to respect observational equivalence classes; it is *precisely*
a right inverse of the world-type quotient projection.  The substantive closure
question — whether selection is internal to the theory — is therefore exactly
the question of whether the corresponding quotient section is internally
realizable.

All results hold for *any* `Selector`, without any internality hypothesis.
-/

namespace NemS

namespace Framework

variable {F : Framework}

/-! ### Theorem 1: selector factors through a section of `toWorldType` -/

/-- Every selector factors through the `ObsEq` quotient via a section of
`toWorldType`.  The selector is the composition `q ∘ toWorldType` for a
(unique) section `q`. -/
theorem selector_quotient_splitting (S : Selector F) :
    ∃ q : Quotient (obsEqSetoid F) → F.Model,
      (∀ wt, toWorldType F (q wt) = wt) ∧ (∀ M, S.sel M = q (toWorldType F M)) := by
  let q : Quotient (obsEqSetoid F) → F.Model :=
    Quotient.lift S.sel (fun M N h => S.cong h)
  refine ⟨q, ?_, ?_⟩
  · intro wt
    induction wt using Quotient.inductionOn with | h M =>
      exact F.toWorldType_eq_iff.mpr (S.inv M)
  · intro M; rfl

/-! ### Theorem 2: the section is unique (∃! form) -/

/-- Every selector determines a *unique* section of `toWorldType` through
which it factors.  This is the forward direction of the Selector ↔ Section
bijection. -/
theorem selector_equiv_section (S : Selector F) :
    ∃! q : Quotient (obsEqSetoid F) → F.Model,
      (∀ wt, toWorldType F (q wt) = wt) ∧ (∀ M, S.sel M = q (toWorldType F M)) := by
  let q : Quotient (obsEqSetoid F) → F.Model :=
    Quotient.lift S.sel (fun M N h => S.cong h)
  use q
  constructor
  · constructor
    · intro wt
      exact Quotient.inductionOn wt (fun M => F.toWorldType_eq_iff.mpr (S.inv M))
    · intro M; rfl
  · intro q' ⟨_, hfact⟩
    funext wt
    exact Quotient.inductionOn wt (fun M => (hfact M).symm)

/-! ### Definition: constructive converse -/

/-- Construct a `Selector` from a section of `toWorldType`.

This is the converse direction of the Selector ↔ Section bijection:
given any right inverse `q` of `toWorldType`, we can build a valid `Selector`
whose underlying map is `M ↦ q (toWorldType F M)`.

The four selector conditions are discharged as follows:
- `inv`  : `toWorldType (q (toWorldType M)) = toWorldType M` (from `hsec`),
           so `q (toWorldType M)` and `M` are in the same `ObsEq` class.
- `idem` : `sel (sel M) = q (toWorldType (q (toWorldType M)))`.
           Apply `hsec` to rewrite `toWorldType (q wt) = wt`, giving
           `q (toWorldType M) = sel M`.
- `cong` : `ObsEq M N → toWorldType M = toWorldType N`, so
           `q (toWorldType M) = q (toWorldType N)`. -/
def quotientSectionToSelector
    (q : Quotient (obsEqSetoid F) → F.Model)
    (hsec : ∀ wt : Quotient (obsEqSetoid F), toWorldType F (q wt) = wt) :
    Selector F where
  sel  := fun M => q (toWorldType F M)
  inv  := fun M => F.toWorldType_eq_iff.mp (hsec (toWorldType F M))
  idem := fun M => congrArg q (hsec (toWorldType F M))
  cong := fun h => congrArg q (F.toWorldType_eq_iff.mpr h)

/-! ### Theorem 3: converse — every section induces a selector -/

/-- Every section of `toWorldType` induces a valid `Selector`.  This is the
converse direction of the Selector ↔ Section bijection. -/
theorem section_defines_selector_general
    (q : Quotient (obsEqSetoid F) → F.Model)
    (hsec : ∀ wt, toWorldType F (q wt) = wt) :
    ∃ S : Selector F, ∀ M, S.sel M = q (toWorldType F M) :=
  ⟨quotientSectionToSelector q hsec, fun _ => rfl⟩

/-! ### Theorem 4: the full bijection (`Equiv` packaging) -/

/-- **Selector–Quotient Splitting Equivalence.**

The type of selectors on `F` is in canonical bijection with the type of
sections of `toWorldType`:
```
  Selector F  ≃  { q : WorldTypes F → F.Model // ∀ wt, toWorldType F (q wt) = wt }
```

**Forward map** (`toFun`): given `S : Selector F`, the section is
`Quotient.lift S.sel ...`, which is well-defined because `S.cong` says
`ObsEq M N → S.sel M = S.sel N`.

**Inverse map** (`invFun`): given a section `(q, hsec)`, the selector is
`quotientSectionToSelector q hsec`.

**Left inverse** (`left_inv`): `(invFun ∘ toFun) S` has `sel M = S.sel M`
by `rfl` (definitional equality), so equality of the `sel` fields closes the
goal; the other fields are propositions and follow by proof irrelevance.

**Right inverse** (`right_inv`): `(toFun ∘ invFun) (q, hsec)` produces
`Quotient.lift (q ∘ toWorldType) ...`.  On generators `wt = ⟦M⟧` this
evaluates to `q (toWorldType M)`, and `hsec` gives `toWorldType (q wt) = wt`,
so the section value at `⟦M⟧` agrees with `q ⟦M⟧`. -/
def selectorSectionEquiv (F : Framework) :
    Selector F ≃
    { q : Quotient (obsEqSetoid F) → F.Model // ∀ wt, toWorldType F (q wt) = wt } where
  toFun S :=
    ⟨Quotient.lift S.sel (fun M N h => S.cong h),
     fun wt => Quotient.inductionOn wt (fun M => F.toWorldType_eq_iff.mpr (S.inv M))⟩
  invFun := fun ⟨q, hsec⟩ => quotientSectionToSelector q hsec
  left_inv S := by
    -- The `sel` fields agree definitionally: `Quotient.lift S.sel ... ⟦M⟧ = S.sel M`.
    -- The other fields are propositions, so they are equal by proof irrelevance.
    cases S with | mk sel inv idem cong =>
      simp only [quotientSectionToSelector]
      congr 1
  right_inv := fun ⟨q, hsec⟩ => by
    -- Need: `Quotient.lift (fun M => q (toWorldType F M)) ... wt = q wt`.
    -- On generators `wt = ⟦M⟧`: `toWorldType F M = ⟦M⟧` by definition, so LHS = RHS.
    ext wt
    induction wt using Quotient.inductionOn with | h M =>
      simp only [quotientSectionToSelector, toWorldType, Quotient.lift_mk]

end Framework

end NemS
