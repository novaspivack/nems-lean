import NemS.Prelude

/-!
# SelfReference.Core.Interface

The **Self-Reference Interface (SRI')** — the minimal two-sorted abstract
structure needed to derive a master fixed-point theorem that subsumes:

- Gödel's diagonal lemma
- Kleene's recursion theorem
- Löb's theorem
- The NEMS diagonal barrier

## Design: the two-sorted SRI'

Classical self-reference involves two distinct levels:

- **Objects** (`Obj`): the things being reasoned about — formulas,
  programs, record statements.  These carry the semantic equivalence `≃`.
- **Codes** (`Code`): syntactic handles for objects — Gödel numbers,
  program indices, record-statement codes.

The two ingredients of self-reference are:

1. **Quotation and evaluation**: `quote : Obj → Code` and
   `run : Code → Code → Obj` — internalize objects as codes and evaluate
   program-codes on input-codes.
2. **Representation**: `repr : (Code → Obj) → Code` — every `Code → Obj`
   transformer has a code, satisfying `run (repr F) c ≃ F c`.

## Axioms

- `repr_spec`: the representation axiom, the type-theoretic analogue of
  Lawvere's weakly point-surjective condition.  This is the **only** axiom
  needed for the primary Master Fixed-Point Theorem (MFP-1).

- `eval_quote`: the re-entry law `run (quote x) (quote x) ≃ x`.  This is
  needed for the unityped fixed-point corollary and for instances that
  require a self-specialization property (Kleene, NEMS).  It is **not**
  needed for MFP-1 itself.

## Instance summary

| Instance | `Obj`  | `Code` | `quote`          | `run e c`     | `repr F`        | `eval_quote`? |
|----------|--------|--------|------------------|---------------|-----------------|---------------|
| Gödel    | `ℕ`    | `ℕ`    | numeral map      | `sub(e, c)`   | diagonalization | axiom (not universal) |
| Kleene   | `ℕ`    | `ℕ`    | `id`             | `smn(e, c)`   | universal index | `smn e e ≃ e` |
| NEMS     | `Prop` | `ℕ`    | record code      | ASR eval      | halting bridge  | ASR round-trip |
| Unityped | `α`    | `α`    | `id` (up to `≃`) | application   | universal repr  | `run x x ≃ x` |

The Gödel instance includes `eval_quote` as an axiom of the abstract
`GodelSystem` structure (the statement `ProvBic (sub n n) n`), but this
axiom is not universally true in concrete arithmetic — it is a hypothesis
on the abstract system.  The Gödel diagonal lemma follows from `repr_spec`
alone via MFP-1.

## Lawvere connection

`repr_spec` is the type-theoretic analogue of Lawvere's "weakly
point-surjective" condition.  The master fixed-point theorem
(`SelfReference.Core.FixedPoint`) is the type-theoretic analogue of
Lawvere's fixed-point theorem, stated in the correct mixed form
`∃ p : Obj, p ≃ F (quote p)`.
-/

namespace SelfReference

universe u v

/-! ## The two-sorted Self-Reference Interface -/

/-- **Minimal Self-Reference Interface (SRI₀′).**  Repr-spec only; sufficient for MFP-1.

Bundles: `Equiv`, `quote`, `run`, `repr`, and `repr_spec`.  No `eval_quote`.
Gödel's diagonal lemma is at this level; Kleene/NEMS need the re-entry extension. -/
class SRI0' (Obj : Type u) (Code : Type v) where
  Equiv       : Obj → Obj → Prop
  equiv_refl  : ∀ x, Equiv x x
  equiv_symm  : ∀ {x y}, Equiv x y → Equiv y x
  equiv_trans : ∀ {x y z}, Equiv x y → Equiv y z → Equiv x z
  quote       : Obj → Code
  run         : Code → Code → Obj
  repr        : (Code → Obj) → Code
  repr_spec   : ∀ (F : Code → Obj) (c : Code), Equiv (run (repr F) c) (F c)

/-- **Self-Reference Interface (SRI′)** — re-entry extension of SRI₀′.

Adds `eval_quote`: `run (quote x) (quote x) ≃ x`.  Needed for the unityped
fixed-point corollary and for Kleene/NEMS instances. -/
class SRI' (Obj : Type u) (Code : Type v) extends SRI0' Obj Code where
  /-- Round-trip law: `run (quote x) (quote x) ≃ x`. -/
  eval_quote : ∀ (x : Obj), Equiv (run (quote x) (quote x)) x

namespace SRI0'

variable {Obj : Type u} {Code : Type v} [S : SRI0' Obj Code]

theorem equiv_is_equivalence : Equivalence (SRI0'.Equiv (Obj := Obj) (Code := Code)) :=
  ⟨SRI0'.equiv_refl, SRI0'.equiv_symm, SRI0'.equiv_trans⟩

def equivSetoid : Setoid Obj where
  r     := SRI0'.Equiv (Obj := Obj) (Code := Code)
  iseqv := equiv_is_equivalence

end SRI0'

namespace SRI'

variable {Obj : Type u} {Code : Type v} [S : SRI' Obj Code]

/-- `Equiv` is an `Equivalence` (inherited from SRI₀′). -/
theorem equiv_is_equivalence : Equivalence (SRI0'.Equiv (Obj := Obj) (Code := Code)) :=
  ⟨SRI0'.equiv_refl, SRI0'.equiv_symm, SRI0'.equiv_trans⟩

/-- The `Setoid` induced by `Equiv`. -/
def equivSetoid : Setoid Obj where
  r     := SRI0'.Equiv (Obj := Obj) (Code := Code)
  iseqv := equiv_is_equivalence

end SRI'

/-! ## The congruent two-sorted SRI'

The master fixed-point theorem requires that `quote` respects `Equiv` in
the sense that equivalent objects produce codes that, when used as inputs
to `run`, yield equivalent outputs.  We capture this as a `quote_cong`
field together with a `run_cong` hypothesis (passed to the theorem, not
baked into the class, since different instances supply it differently). -/

/-- A **congruent SRI'** extends `SRI'` with:
- `quote_cong`: equivalent objects have codes that `run` treats equivalently.

Concretely, `quote_cong` says that if `x ≃ y` then
`run (quote x) (quote x) ≃ run (quote y) (quote y)`.
This follows from `eval_quote` + congruence of `run`, but we state it
directly to avoid requiring a full `run_cong` in the class. -/
class CSRI' (Obj : Type u) (Code : Type v) extends SRI' Obj Code where
  /-- `quote` respects `Equiv` in the sense that `run (quote x) (quote x) ≃ run (quote y) (quote y)`
  whenever `x ≃ y`. -/
  quote_run_cong : ∀ {x y : Obj}, Equiv x y →
      Equiv (run (quote x) (quote x)) (run (quote y) (quote y))

namespace CSRI'

variable {Obj : Type u} {Code : Type v} [S : CSRI' Obj Code]

end CSRI'

/-! ## The unityped SRI (special case, alias for backward compatibility)

When `Obj = Code = α` and `quote` is identity up to `Equiv`, the two-sorted
interface collapses to the unityped interface.  We provide this as a separate
typeclass so that existing code using `SRI α` and `CSRI α` continues to work,
and so that the unityped instances (Gödel, Kleene) can be stated cleanly. -/

/-- The **unityped Self-Reference Interface** (special case with `Obj = Code = α`).

This is the original SRI.  It is a special case of `SRI' α α` where `Equiv`
serves as both the object-level equivalence and the code-level equivalence.

The unityped setting is appropriate when the object language and the code
language coincide — as in Gödel numbering (formulas are numbers) and Kleene
indices (programs are numbers). -/
class SRI (α : Type u) where
  /-- Extensional equivalence on terms. -/
  Equiv : α → α → Prop
  /-- `Equiv` is reflexive. -/
  equiv_refl  : ∀ x, Equiv x x
  /-- `Equiv` is symmetric. -/
  equiv_symm  : ∀ {x y}, Equiv x y → Equiv y x
  /-- `Equiv` is transitive. -/
  equiv_trans : ∀ {x y z}, Equiv x y → Equiv y z → Equiv x z
  /-- Quotation: internalize a term as its own code. -/
  quote : α → α
  /-- Two-argument evaluation: run "program" `e` on "input" `c`. -/
  run   : α → α → α
  /-- Representation: any transformer `α → α` has a code. -/
  repr  : (α → α) → α
  /-- Representation axiom: `run (repr F) c ≃ F c`. -/
  repr_spec : ∀ (F : α → α) (c : α), Equiv (run (repr F) c) (F c)
  /-- Round-trip law: `run (quote x) (quote x) ≃ x`. -/
  eval_quote : ∀ (x : α), Equiv (run (quote x) (quote x)) x

/-- Every `SRI α` induces an `SRI' α α`. -/
instance sriToSRI' {α : Type u} [S : SRI α] : SRI' α α where
  Equiv       := S.Equiv
  equiv_refl  := S.equiv_refl
  equiv_symm  := S.equiv_symm
  equiv_trans := S.equiv_trans
  quote       := S.quote
  run         := S.run
  repr        := S.repr
  repr_spec   := S.repr_spec
  eval_quote  := S.eval_quote

namespace SRI

variable {α : Type u} [S : SRI α]

/-- `Equiv` is an `Equivalence`. -/
theorem equiv_is_equivalence : Equivalence (SRI.Equiv (α := α)) :=
  ⟨SRI.equiv_refl, SRI.equiv_symm, SRI.equiv_trans⟩

/-- The `Setoid` induced by `Equiv`. -/
def equivSetoid : Setoid α where
  r     := SRI.Equiv
  iseqv := equiv_is_equivalence

end SRI

/-- The **unityped congruent SRI** (special case of `CSRI'` with `Obj = Code = α`).

Extends `SRI α` with `quote_cong`: `quote` respects `Equiv`. -/
class CSRI (α : Type u) extends SRI α where
  /-- `SRI.quote` respects `SRI.Equiv`. -/
  quote_cong : ∀ {x y : α}, SRI.Equiv x y → SRI.Equiv (SRI.quote x) (SRI.quote y)

/-- Every `CSRI α` induces a `CSRI' α α`. -/
instance csriToCSRI' {α : Type u} [S : CSRI α] : CSRI' α α where
  Equiv       := S.Equiv
  equiv_refl  := S.equiv_refl
  equiv_symm  := S.equiv_symm
  equiv_trans := S.equiv_trans
  quote       := S.quote
  run         := S.run
  repr        := S.repr
  repr_spec   := S.repr_spec
  eval_quote  := S.eval_quote
  quote_run_cong := fun hxy =>
    -- Chain: run (quote x)(quote x) ≃ x ≃ y ≃ run (quote y)(quote y)
    -- using eval_quote on both sides and the hypothesis x ≃ y.
    S.equiv_trans (S.eval_quote _) (S.equiv_trans hxy (S.equiv_symm (S.eval_quote _)))

end SelfReference
