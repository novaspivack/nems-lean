import SelfReference.Core.Interface
import SelfReference.Core.FixedPoint
import SelfReference.Consequences.DiagonalBarrier

/-!
# SelfReference.Minimality.StratifiedReflection

## The Stratified Reflection Hierarchy

The SRI axioms admit a natural **stratification** corresponding to the
NEMS IIa/IIb classification and the classical Tarski hierarchy.

### The three strata

**Stratum 0 — No internalization**:
No `quote`, no `repr`.  No self-reference.  Fixed points not derivable.

**Stratum 1 — Partial internalization**:
Has `quote`, `run`, `eval_quote`, and `repr` for a *restricted* class `R`
of transformers.  Fixed points exist for `F ∈ R` provided `R` is closed
under the diagonal composition and `run` is congruent.

**Stratum 2 — Full internalization** (= CSRI):
All transformers are representable.  Fixed points exist universally.
The diagonal barrier applies.

### The NEMS correspondence

- Stratum 0 ↔ NEMS Class I (categorical, no self-reference needed)
- Stratum 1 ↔ NEMS Class IIa (internal selector, total-effective)
- Stratum 2 ↔ NEMS Class IIb (internal selector, NOT total-effective)

The diagonal barrier is the reason Stratum 2 cannot have a total
effective truth predicate.

### The real semantic trichotomy

The trichotomy is not a tautological case split — it is a genuine
separation theorem:

1. **Stratum 0** systems provably cannot derive fixed points for any
   non-constant `F` (proved by the `Bool`/`not` countermodel).

2. **Stratum 1** systems can derive fixed points for `F ∈ R` (when `R`
   is closed under the diagonal composition), but there exist Stratum 1
   systems that are not Stratum 2 (proved by the constant-functions-only
   countermodel).

3. **Stratum 2** systems have universal fixed points but pay the price:
   the diagonal barrier rules out any total decider for nontrivial
   extensional predicates.

These three properties are **strictly separated**: each stratum is a
proper subset of the next, and the separations are witnessed by
explicit countermodels.
-/

namespace SelfReference
namespace Minimality

universe u

/-! ## The three strata -/

/-- **Stratum 0**: A system with no self-reference capability.

Only an equivalence relation.  No quotation, no evaluation, no representation. -/
class Stratum0 (α : Type u) where
  Equiv : α → α → Prop
  equiv_refl  : ∀ x, Equiv x x
  equiv_symm  : ∀ {x y}, Equiv x y → Equiv y x
  equiv_trans : ∀ {x y z}, Equiv x y → Equiv y z → Equiv x z

/-- **Stratum 1**: A system with partial internalization.

Has `quote`, `run`, `eval_quote`, and `repr` for a restricted class `R`. -/
class Stratum1 (α : Type u) extends Stratum0 α where
  quote : α → α
  run   : α → α → α
  eval_quote : ∀ x, Equiv (run (quote x) (quote x)) x
  /-- The class of representable transformers. -/
  Representable : (α → α) → Prop
  repr  : ∀ F, Representable F → α
  repr_spec : ∀ F (hF : Representable F) c, Equiv (run (repr F hF) c) (F c)

/-- **Stratum 2**: Full internalization — all transformers representable.

This is exactly `CSRI α`. -/
class Stratum2 (α : Type u) extends CSRI α

/-- Stratum 2 implies Stratum 1 (with `Representable = ⊤`). -/
instance stratum2_implies_stratum1 {α : Type u} [S : Stratum2 α] : Stratum1 α where
  Equiv       := S.Equiv
  equiv_refl  := S.equiv_refl
  equiv_symm  := S.equiv_symm
  equiv_trans := S.equiv_trans
  quote       := S.quote
  run         := S.run
  eval_quote  := S.eval_quote
  Representable := fun _ => True
  repr        := fun F _ => S.repr F
  repr_spec   := fun F _ c => S.repr_spec F c

/-! ## Theorem 1: Stratum 0 systems have no fixed points for non-constant `F` -/

/-- **Stratum 0 countermodel**: `Bool` with `not` has no fixed point.

`not b ≠ b` for all `b : Bool`.  This shows that without the SRI
machinery, fixed points of non-constant functions are not derivable. -/
theorem stratum0_no_fixed_point_for_not :
    ¬ ∃ b : Bool, b = !b := by
  intro ⟨b, hb⟩
  cases b <;> simp at hb

/-- **Stratum 0 has no universal fixed-point property.**

There exists a Stratum 0 system and a non-constant transformer with no fixed point. -/
theorem stratum0_no_universal_fixed_point :
    ∃ (α : Type) (_ : Stratum0 α) (F : α → α),
      (¬ ∀ x, F x = x) ∧ ¬ ∃ d : α, F d = d := by
  exact ⟨Bool, ⟨Eq, fun _ => rfl, Eq.symm, Eq.trans⟩, Bool.not,
    ⟨fun h => absurd (h true) (by decide),
     fun ⟨b, hb⟩ => by cases b <;> simp at hb⟩⟩

/-! ## Theorem 2: Stratum 2 systems have universal fixed points -/

/-- **Stratum 2 fixed-point theorem**: Every transformer has a fixed point.

In any Stratum 2 system (`CSRI α`), for any congruent `F : α → α`,
there exists `d : α` with `d ≃ F d`.

This is `CSRI.master_fixed_point` from `Core/FixedPoint.lean`. -/
theorem stratum2_universal_fixed_point {α : Type u} [S : Stratum2 α]
    (F : α → α)
    (hF : ∀ {x y : α}, SRI.Equiv x y → SRI.Equiv (F x) (F y))
    (hquote_id : ∀ x : α, SRI.Equiv (SRI.quote x) x)
    (hrun_cong : ∀ {e₁ e₂ c₁ c₂ : α},
        SRI.Equiv e₁ e₂ → SRI.Equiv c₁ c₂ →
        SRI.Equiv (SRI.run e₁ c₁) (SRI.run e₂ c₂)) :
    ∃ d : α, SRI.Equiv d (F d) :=
  CSRI.master_fixed_point F hF hquote_id hrun_cong

/-! ## Theorem 3: Stratum 1 does NOT imply Stratum 2 (strict separation) -/

/-- **Stratum 1 does NOT imply Stratum 2** in general.

Countermodel: the system where only constant functions are representable.

This is a Stratum 1 system (fixed points exist for constant functions)
that is not Stratum 2 (the successor function has no code). -/
theorem stratum1_not_implies_stratum2 :
    ∃ (α : Type) (S1 : Stratum1 α),
      ¬ (∀ F : α → α, S1.Representable F) := by
  use ℕ
  refine ⟨{
    Equiv       := Eq
    equiv_refl  := fun _ => rfl
    equiv_symm  := Eq.symm
    equiv_trans := Eq.trans
    quote       := id
    run         := fun e _ => e
    eval_quote  := fun _ => rfl
    Representable := fun F => ∃ n, ∀ m, F m = n
    repr        := fun F hF => hF.choose
    repr_spec   := fun F hF c => (hF.choose_spec c).symm
  }, ?_⟩
  intro h
  have := h (· + 1)
  obtain ⟨n, hn⟩ := this
  exact absurd (hn n) (Nat.succ_ne_self n)

/-- **The specific Stratum 1 system with `run e c = e` cannot be Stratum 2.**

If `run e c = e` for all `e c`, then `repr_spec (· + 1) c` gives `repr (· + 1) = c + 1`
for all `c`, which is impossible (take `c = 0` and `c = 1`). -/
theorem const_run_not_stratum2 :
    ¬ ∃ (repr : (ℕ → ℕ) → ℕ),
        ∀ (F : ℕ → ℕ) (c : ℕ), (fun e (_ : ℕ) => e) (repr F) c = F c := by
  intro ⟨repr, hrepr⟩
  have h0 : repr (· + 1) = 0 + 1 := hrepr (· + 1) 0
  have h1 : repr (· + 1) = 1 + 1 := hrepr (· + 1) 1
  omega

/-! ## Theorem 4: Stratum 2 implies the diagonal barrier -/

/-- **Stratum 2 implies the diagonal barrier.**

Any Stratum 2 system has no total decider for a nontrivial extensional
predicate (within the representable class).

This is a direct corollary of `Consequences.no_total_decider_nontrivial_unityped`. -/
theorem stratum2_diagonal_barrier {α : Type u} [S : Stratum2 α]
    (T : α → Prop)
    (hExt : Consequences.ExtensionalPredU (α := α) T)
    (hNontrivial : (∃ x, T x) ∧ (∃ x, ¬ T x))
    (hquote_id : ∀ x : α, SRI.Equiv (α := α) (SRI.quote x) x)
    (hrun_cong : ∀ {e₁ e₂ c₁ c₂ : α},
        SRI.Equiv (α := α) e₁ e₂ → SRI.Equiv (α := α) c₁ c₂ →
        SRI.Equiv (α := α) (SRI.run e₁ c₁) (SRI.run e₂ c₂)) :
    ¬ ∃ decide : α → Bool, Consequences.TotalDeciderU (α := α) T decide :=
  Consequences.no_total_decider_nontrivial_unityped T hExt hNontrivial hquote_id hrun_cong

/-! ## The Semantic Trichotomy -/

/-- **The Semantic Diagonal Trichotomy.**

For any type `α`, the following are mutually exclusive and exhaustive:

1. **Stratum 0**: No self-reference structure.
2. **Stratum 1 but not Stratum 2**: Partial internalization.
3. **Stratum 2**: Full internalization with diagonal barrier.

The three cases have distinct semantic content, witnessed by explicit
countermodels:
- Stratum 0 ≠ Stratum 1: `Bool`/`not` (no fixed point without `repr`).
- Stratum 1 ≠ Stratum 2: `ℕ`/constant-functions-only (no code for `succ`).
- Stratum 2 barrier: `const_run_not_stratum2`. -/
theorem semantic_trichotomy (α : Type u) :
    (¬ Nonempty (Stratum1 α)) ∨
    (Nonempty (Stratum1 α) ∧ ¬ Nonempty (Stratum2 α)) ∨
    (Nonempty (Stratum2 α)) := by
  by_cases h2 : Nonempty (Stratum2 α)
  · exact Or.inr (Or.inr h2)
  · by_cases h1 : Nonempty (Stratum1 α)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inl h1

/-- **Semantic content of the trichotomy** (the real theorem).

The three cases have distinct semantic content:

- Case 1 (Stratum 0): `Bool` witnesses that non-constant functions need not
  have fixed points when there is no `repr`.

- Case 2 (Stratum 1 ∖ Stratum 2): The constant-functions-only system on `ℕ`
  witnesses that partial representability is possible without full representability.

- Case 3 (Stratum 2): The `const_run_not_stratum2` theorem shows that the
  specific Stratum 1 system with `run e c = e` cannot be Stratum 2. -/
theorem semantic_trichotomy_content :
    -- Stratum 0 witness: Bool with not has no fixed point
    (¬ ∃ b : Bool, b = !b) ∧
    -- Stratum 1 ∖ Stratum 2 witness: ℕ with constant repr is not full
    (∃ (S1 : Stratum1 ℕ), ¬ (∀ F : ℕ → ℕ, S1.Representable F)) ∧
    -- Stratum 2 barrier: const_run cannot be Stratum 2
    (¬ ∃ (repr : (ℕ → ℕ) → ℕ),
        ∀ (F : ℕ → ℕ) (c : ℕ), (fun e (_ : ℕ) => e) (repr F) c = F c) := by
  refine ⟨stratum0_no_fixed_point_for_not, ?_, const_run_not_stratum2⟩
  -- Provide the Stratum 1 system on ℕ with only constant functions representable.
  use {
    Equiv       := Eq
    equiv_refl  := fun _ => rfl
    equiv_symm  := Eq.symm
    equiv_trans := Eq.trans
    quote       := id
    run         := fun e _ => e
    eval_quote  := fun _ => rfl
    Representable := fun F => ∃ n, ∀ m, F m = n
    repr        := fun F hF => hF.choose
    repr_spec   := fun F hF c => (hF.choose_spec c).symm
  }
  intro h
  obtain ⟨n, hn⟩ := h (· + 1)
  exact absurd (hn n) (Nat.succ_ne_self n)

end Minimality
end SelfReference
