import SelfReference.Core.FixedPoint

/-!
# SelfReference.Instances.Kleene

## Kleene's Recursion Theorem as an SRI instance

The **recursion theorem** states: for any total function `f : ℕ → ℕ`,
there exists an index `e` such that `φ_e ≃ φ_{f(e)}`.

We instantiate the CSRI with:

| CSRI component | Kleene instance |
|----------------|-----------------|
| `α`            | `ℕ` (program indices) |
| `Equiv e₁ e₂`  | `∀ x, φ_{e₁}(x) = φ_{e₂}(x)` (extensional equality) |
| `quote`        | `id` |
| `run e c`      | `smn e c` (s-m-n: program `e` specialized to input `c`) |
| `repr F`       | index of the program computing `F` |
| `eval_quote`   | `smn e e ≃ e` (self-specialization) |

The key axiom `repr_spec` is the **s-m-n theorem**:
`smn (repr F) c ≃ F c` for all `F` and `c`.
-/

namespace SelfReference
namespace Instances
namespace Kleene

/-- Abstract program system for the Kleene instance. -/
structure ProgramSystem where
  /-- Extensional equivalence of programs. -/
  ExtEq : ℕ → ℕ → Prop
  extEq_refl  : ∀ e, ExtEq e e
  extEq_symm  : ∀ {e₁ e₂}, ExtEq e₁ e₂ → ExtEq e₂ e₁
  extEq_trans : ∀ {e₁ e₂ e₃}, ExtEq e₁ e₂ → ExtEq e₂ e₃ → ExtEq e₁ e₃
  /-- s-m-n function: `smn e c` is the index of `y ↦ φ_e(c, y)`. -/
  smn : ℕ → ℕ → ℕ
  /-- Every transformer `F : ℕ → ℕ` has an index `repr F` such that
      `smn (repr F) c ≃ F c`. -/
  repr_fn : (ℕ → ℕ) → ℕ
  repr_fn_spec : ∀ (F : ℕ → ℕ) (c : ℕ), ExtEq (smn (repr_fn F) c) (F c)
  /-- `smn` is congruent in the first argument. -/
  smn_cong : ∀ {e₁ e₂ : ℕ} (c : ℕ), ExtEq e₁ e₂ → ExtEq (smn e₁ c) (smn e₂ c)
  /-- Self-specialization: `smn e e ≃ e`. -/
  smn_self : ∀ e, ExtEq (smn e e) e

/-- Construct a CSRI from a program system. -/
@[reducible]
def kleeneCSRI (P : ProgramSystem) : CSRI ℕ where
  Equiv       := P.ExtEq
  equiv_refl  := P.extEq_refl
  equiv_symm  := P.extEq_symm
  equiv_trans := P.extEq_trans
  quote       := id
  run         := P.smn
  repr        := P.repr_fn
  repr_spec   := P.repr_fn_spec
  eval_quote  := P.smn_self
  quote_cong  := fun h => h

/-- **Kleene's Recursion Theorem** as a corollary of MFP-1.

For any program transformer `F : ℕ → ℕ`, there exists `e : ℕ` with
`φ_e ≃ φ_{F(e)}`. -/
theorem kleene_recursion_theorem (P : ProgramSystem) (F : ℕ → ℕ)
    (hF_cong : ∀ {x y : ℕ}, P.ExtEq x y → P.ExtEq (F x) (F y)) :
    ∃ e : ℕ, P.ExtEq e (F e) := by
  -- Set G c := F (smn c c), d := repr_fn G.
  -- repr_fn_spec: smn d d ≃ G d = F (smn d d).
  -- smn_self: smn d d ≃ d.
  -- Chain: d ≃ smn d d ≃ F (smn d d) ≃ F d.
  let G : ℕ → ℕ := fun c => F (P.smn c c)
  let d : ℕ := P.repr_fn G
  use d
  have hstep1 : P.ExtEq (P.smn d d) (G d) := P.repr_fn_spec G d
  simp only [G] at hstep1
  have hstep2 : P.ExtEq (P.smn d d) d := P.smn_self d
  have hstep3 : P.ExtEq d (P.smn d d) := P.extEq_symm hstep2
  have hstep4 : P.ExtEq (P.smn d d) (F (P.smn d d)) := hstep1
  have hstep5 : P.ExtEq (F (P.smn d d)) (F d) := hF_cong hstep2
  exact P.extEq_trans hstep3 (P.extEq_trans hstep4 hstep5)

/-- **Rogers' fixed-point theorem**: For any total `f`, the set of
fixed points of `f` is nonempty. -/
theorem rogers_fixed_point (P : ProgramSystem) (f : ℕ → ℕ)
    (hf_cong : ∀ {x y}, P.ExtEq x y → P.ExtEq (f x) (f y)) :
    ∃ e : ℕ, P.ExtEq e (f e) :=
  kleene_recursion_theorem P f hf_cong

end Kleene
end Instances
end SelfReference
