import SelfReference.Core.Representability

/-!
# SelfReference.Core.FixedPoint

## The Master Fixed-Point Theorem (MFP-1)

The primary theorem is stated in the **two-sorted** form:

**Theorem** (`master_fixed_point`): In any `SRI' Obj Code` system, for any
transformer `F : Code → Obj`, there exists `p : Obj` such that
`p ≃ F (quote p)`.

This is the correct abstract form of the diagonal lemma:
- Gödel: `ψ ↔ F(⌜ψ⌝)` (a formula equivalent to `F` applied to its own code).
- Kleene: `e ≃ φ_{f(e)}` (a program index equivalent to `f` applied to itself).
- NEMS: a record truth equivalent to the truth of its own coded statement.

The **unityped corollary** (`master_fixed_point`) in the `CSRI` namespace
recovers the classical `d ≃ F d` fixed point for systems where `Obj = Code = α`
and `quote` is identity up to `≃`.

## Proof of the primary theorem (two-sorted)

Set `G c := F (quote (run c c))` and `d := repr G : Code`.
Let `p := run d d : Obj`.

By `repr_spec` at `c = d`:
  `run d d ≃ G d = F (quote (run d d)) = F (quote p)`.

So `p ≃ F (quote p)` — the mixed fixed point.  The proof is a single
application of `repr_spec`.  No congruence hypothesis on `F` is needed.

## Proof of the unityped corollary

The unityped corollary additionally uses `eval_quote` (to establish
`run (quote d) (quote d) ≃ d`) and `quote_cong` (to chain
`F (quote p) ≃ F p`).  These are needed only for the collapse from
`p ≃ F (quote p)` to `p ≃ F p` in the unityped setting.
-/

namespace SelfReference

universe u v

/-! ## The primary two-sorted Master Fixed-Point Theorem -/

namespace CSRI'

variable {Obj : Type u} {Code : Type v} [S : CSRI' Obj Code]

/-- **Master Fixed-Point Theorem (MFP-1) — two-sorted form.**

For any transformer `F : Code → Obj`, there exists `p : Obj` with
`S.Equiv p (F (S.quote p))`.

This is the mixed fixed point: `p` is an object semantically equivalent
to `F` applied to the code of `p`.  The proof uses only `repr_spec`.

**Proof**: Set `G c := F (quote (run c c))`, `d := repr G`.
Then `run d d ≃ G d = F (quote (run d d)) = F (quote p)` where `p = run d d`. -/
theorem master_fixed_point
    (F : Code → Obj) :
    ∃ p : Obj, S.Equiv p (F (S.quote p)) :=
  let G : Code → Obj := fun c => F (S.quote (S.run c c))
  ⟨S.run (S.repr G) (S.repr G), S.repr_spec G (S.repr G)⟩

/-- **Code-level fixed point** (two-sorted form, alternative formulation).

There exists `d : Code` such that
`S.run d (S.quote (S.run d d)) ≃ F (S.quote (S.run d d))`.

This is the fixed point at the code level: `run d (quote (run d d)) ≃ F (quote (run d d))`. -/
theorem master_fixed_point_code
    (F : Code → Obj)
    (hF : ∀ {x y : Obj}, S.Equiv x y → S.Equiv (F (S.quote x)) (F (S.quote y))) :
    ∃ d : Code,
      S.Equiv (S.run d (S.quote (S.run d d))) (F (S.quote (S.run d d))) :=
  ⟨diag F, diag_code_fixed_point F (fun h => hF h)⟩

end CSRI'

/-! ## The unityped Master Fixed-Point Theorem -/

namespace CSRI

variable {α : Type u} [S : CSRI α]

/-- **Master Fixed-Point Theorem (MFP-1) — unityped form.**

For any congruent transformer `F : α → α`, there exists `d : α` with
`S.Equiv d (F d)`.

This is a corollary of the two-sorted `CSRI'.master_fixed_point` for the
special case `Obj = Code = α` with `quote x ≃ x` (identity quotation). -/
theorem master_fixed_point
    (F : α → α)
    (hF : ∀ {x y : α}, S.Equiv x y → S.Equiv (F x) (F y))
    (hquote_id : ∀ x : α, S.Equiv (S.quote x) x)
    (hrun_cong : ∀ {e₁ e₂ c₁ c₂ : α},
        S.Equiv e₁ e₂ → S.Equiv c₁ c₂ →
        S.Equiv (S.run e₁ c₁) (S.run e₂ c₂)) :
    ∃ d : α, S.Equiv d (F d) := by
  -- Set G c := F (quote (run c c)), d := repr G.
  -- The chain: d ≃ run d (quote d) ≃ F (quote (run (quote d)(quote d))) ≃ F (quote d) ≃ F d.
  -- Steps use: repr_spec, eval_quote, quote_cong, hF, hquote_id, hrun_cong.
  let G : α → α := fun c => F (S.quote (S.run c c))
  let d : α := S.repr G
  use d
  have hA : S.Equiv (S.run (S.quote d) (S.quote d)) d := S.eval_quote d
  have hB : S.Equiv (S.quote d) d := hquote_id d
  have hC : S.Equiv (S.run d (S.quote d)) (S.run (S.quote d) (S.quote d)) :=
    hrun_cong (S.equiv_symm hB) (S.equiv_refl _)
  have hD : S.Equiv d (S.run d (S.quote d)) := S.equiv_symm (S.equiv_trans hC hA)
  have hE : S.Equiv (S.run d (S.quote d)) (F (S.quote (S.run (S.quote d) (S.quote d)))) :=
    S.repr_spec G (S.quote d)
  have hF1 : S.Equiv (S.quote (S.run (S.quote d) (S.quote d))) (S.quote d) := S.quote_cong hA
  have hG : S.Equiv (F (S.quote (S.run (S.quote d) (S.quote d)))) (F (S.quote d)) := hF hF1
  have hH : S.Equiv (F (S.quote d)) (F d) := hF hB
  exact S.equiv_trans hD (S.equiv_trans hE (S.equiv_trans hG hH))

/-- **Code-level fixed point** (unityped form, without `hquote_id`).

There exists `d : α` with `S.Equiv (S.run d (S.quote d)) (F (S.quote d))`. -/
theorem master_fixed_point_code
    (F : α → α)
    (hF : ∀ {x y : α}, S.Equiv x y → S.Equiv (F x) (F y)) :
    ∃ d : α, S.Equiv (S.run d (S.quote d)) (F (S.quote d)) :=
  ⟨diagU F, diagU_code_fixed_point F S.quote_cong hF⟩

end CSRI

end SelfReference
