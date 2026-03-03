import SelfReference.Core.Interface

/-!
# SelfReference.Core.Representability

Representability predicates and the diagonal construction for the
two-sorted SRI'.

## Key definitions

- `Representable F` : transformer `F : Code → Obj` has a code satisfying `repr_spec`.

- `diag F` : the **diagonal code** of `F : Code → Obj`, defined as
  `repr (fun c => F (quote (run c c)))`.

- `diag_spec` : `run (diag F) c ≃ F (quote (run c c))` for all `c : Code`.

## The diagonal construction

Let `d : Code := diag F = repr (fun c => F (quote (run c c)))`.

By `diag_spec` with `c = quote (run d d)`:
  `run d (quote (run d d)) ≃ F (quote (run (quote (run d d)) (quote (run d d))))`

By `eval_quote (run d d)`:
  `run (quote (run d d)) (quote (run d d)) ≃ run d d`

So the diagonal construction produces a code `d` such that:
  `run d (quote (run d d)) ≃ F (quote (run d d))`

This is the **code-level fixed point**: the object `run d (quote (run d d))`
satisfies `p ≃ F (quote p)` where `p = run d (quote (run d d))`.
-/

namespace SelfReference

universe u v

variable {Obj : Type u} {Code : Type v} [S : SRI' Obj Code]

/-- A transformer `F : Code → Obj` is **representable** if there exists a
code `c : Code` such that `S.Equiv (S.run c d) (F d)` for all `d : Code`. -/
def Representable (F : Code → Obj) : Prop :=
  ∃ c : Code, ∀ d : Code, S.Equiv (S.run c d) (F d)

/-- Every transformer is representable: `S.repr F` witnesses it. -/
theorem all_representable (F : Code → Obj) : Representable F :=
  ⟨S.repr F, fun d => S.repr_spec F d⟩

/-- The **diagonal code** of a transformer `F : Code → Obj`.

`diag F := S.repr (fun c => F (S.quote (S.run c c)))`.

This is a `Code` that, when run on any input `c : Code`, produces
`F (S.quote (S.run c c))`. -/
def diag (F : Code → Obj) : Code :=
  S.repr (fun c => F (S.quote (S.run c c)))

/-- Running `diag F` on input `c` gives `F (S.quote (S.run c c))`. -/
theorem diag_spec (F : Code → Obj) (c : Code) :
    S.Equiv (S.run (diag F) c) (F (S.quote (S.run c c))) :=
  S.repr_spec (fun c => F (S.quote (S.run c c))) c

/-- **Code-level fixed point** (two-sorted form).

Let `d := diag F` and `p := SRI'.run d (SRI'.quote (SRI'.run d d))`.
Then `p ≃ F (SRI'.quote (SRI'.run d d))`.

This is the **mixed fixed point at the code level**: the object
`p = run d (quote (run d d))` satisfies `p ≃ F (quote (run d d))`.

Requires `F` to be congruent w.r.t. `S.Equiv`. -/
theorem diag_code_fixed_point (F : Code → Obj)
    (hF_cong : ∀ {x y : Obj}, S.Equiv x y → S.Equiv (F (S.quote x)) (F (S.quote y))) :
    let d := diag F
    S.Equiv
      (S.run d (S.quote (S.run d d)))
      (F (S.quote (S.run d d))) := by
  simp only
  let d := diag F
  -- diag_spec at c = quote (run d d) gives the first step.
  -- eval_quote (run d d) gives the round-trip, used via hF_cong to close the chain.
  have step1 : S.Equiv
      (S.run d (S.quote (S.run d d)))
      (F (S.quote (S.run (S.quote (S.run d d)) (S.quote (S.run d d))))) :=
    diag_spec F (S.quote (S.run d d))
  have step2 : S.Equiv
      (S.run (S.quote (S.run d d)) (S.quote (S.run d d)))
      (S.run d d) :=
    S.eval_quote (S.run d d)
  have step3 : S.Equiv
      (F (S.quote (S.run (S.quote (S.run d d)) (S.quote (S.run d d)))))
      (F (S.quote (S.run d d))) :=
    hF_cong step2
  exact S.equiv_trans step1 step3

/-! ## Unityped versions (backward compatibility)

For the unityped `SRI α` setting, the diagonal construction is the same
but with `Obj = Code = α`. -/

variable {α : Type u} [S' : SRI α]

/-- The **unityped diagonal code** of a transformer `F : α → α`. -/
def diagU (F : α → α) : α :=
  SRI.repr (fun c => F (SRI.quote (SRI.run c c)))

/-- Running `diagU F` on input `c` gives `F (SRI.quote (SRI.run c c))`. -/
theorem diagU_spec (F : α → α) (c : α) :
    SRI.Equiv (SRI.run (diagU F) c) (F (SRI.quote (SRI.run c c))) :=
  SRI.repr_spec (fun c => F (SRI.quote (SRI.run c c))) c

/-- **Code-level fixed point** (unityped form).

`SRI.run (diagU F) (SRI.quote (diagU F)) ≃ F (SRI.quote (diagU F))`.

Requires `SRI.quote` and `F` to be congruent. -/
theorem diagU_code_fixed_point (F : α → α)
    (hquote_cong : ∀ {x y : α}, SRI.Equiv x y → SRI.Equiv (SRI.quote x) (SRI.quote y))
    (hF_cong : ∀ {x y : α}, SRI.Equiv x y → SRI.Equiv (F x) (F y)) :
    SRI.Equiv (SRI.run (diagU F) (SRI.quote (diagU F))) (F (SRI.quote (diagU F))) := by
  have step1 : SRI.Equiv
      (SRI.run (diagU F) (SRI.quote (diagU F)))
      (F (SRI.quote (SRI.run (SRI.quote (diagU F)) (SRI.quote (diagU F))))) :=
    diagU_spec F (SRI.quote (diagU F))
  have step2 : SRI.Equiv (SRI.run (SRI.quote (diagU F)) (SRI.quote (diagU F))) (diagU F) :=
    SRI.eval_quote (diagU F)
  have step3 : SRI.Equiv
      (SRI.quote (SRI.run (SRI.quote (diagU F)) (SRI.quote (diagU F))))
      (SRI.quote (diagU F)) :=
    hquote_cong step2
  have step4 : SRI.Equiv
      (F (SRI.quote (SRI.run (SRI.quote (diagU F)) (SRI.quote (diagU F)))))
      (F (SRI.quote (diagU F))) :=
    hF_cong step3
  exact SRI.equiv_trans step1 step4

end SelfReference
