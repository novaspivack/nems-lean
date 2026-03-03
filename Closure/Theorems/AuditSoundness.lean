import Closure.Core.Internal
import Closure.Core.Selector

/-!
# Closure.Theorems.AuditSoundness

**Audit soundness:** the core audit theorem is **factorization through the quotient**:
any predicate decidable purely on world-types is observationally invariant.
So any decider for a non-invariant predicate cannot factor through world-types—
it must depend on a choice of representative (selector). That is the real bite.

* **Badge 1 — `audit_soundness` / `not_invariant_implies_not_decidable_on_world_type`:**
  DecidableOnWorldType P ⇒ Invariant P (and contrapositive). No Choice; constructive.

* **Selector existence** is stated separately as **`selector_exists_classical`**: under
  classical Choice, a section of the quotient exists. This is *not* a consequence
  of non-invariance; it is the same for any semantics. The interesting theorem
  is that non-invariant predicates are *not* decidable on world-types.

* **Badge 2 — Internal outsourcing:** When "internal" is instantiated (computable,
  definable) and the semantics has effective presentation or canonicalization,
  internal decider for a non-invariant P implies internal symmetry-breaking
  (internal selector or canon). See `DeciderImpliesInternalSelector` and
  `Closure.Core.Canonicalization` / `EffectiveSemantics` for the nailed version.
-/

set_option autoImplicit false

namespace Closure

universe u v

variable {World : Type u} {Obs : Type v} (S : ObsSemantics World Obs)

/-- A predicate `P` on worlds is **decidable on world-types** if there
exists a function on world-types that agrees with `P` on representatives. -/
def DecidableOnWorldType (P : World → Prop) : Prop :=
  ∃ f : S.WorldType → Prop, ∀ w, f (S.toWorldType w) ↔ P w

/-- **Audit soundness (factorization through quotient).** If `P` is decidable
on world-types, then `P` is observationally invariant. So any predicate that
is not invariant cannot be decided at the world-type level without a choice
of representative. This is the core audit theorem; no Choice used. -/
theorem audit_soundness (P : World → Prop) (hDec : DecidableOnWorldType S P) :
    S.Invariant P := by
  obtain ⟨f, hf⟩ := hDec
  intro w₁ w₂ h
  have heq : S.toWorldType w₁ = S.toWorldType w₂ := Quotient.sound h
  rw [← hf w₁, ← hf w₂, heq]

/-- **Audit soundness (contrapositive).** If `P` is not invariant, then `P`
is not decidable on world-types—no decider factors through the quotient.
This is the sharp "no free bits" formulation: distinguishing equivalent
worlds requires extra structure. -/
theorem not_invariant_implies_not_decidable_on_world_type
    (P : World → Prop) (h : ¬ S.Invariant P) :
    ¬ DecidableOnWorldType S P :=
  fun hDec => h (audit_soundness S P hDec)

/-! ## Classical selector existence (Choice; not a consequence of non-invariance) -/

/-- A **total decider** for `P` is a Boolean-valued function that agrees with `P`. -/
def TotalDecider (P : World → Prop) (δ : World → Bool) : Prop :=
  ∀ w, (δ w = true ↔ P w)

/-- In every world-type there is at least one representative. -/
theorem exists_rep (t : S.WorldType) : ∃ w : World, S.toWorldType w = t :=
  Quotient.exists_rep (s := S.obsEquivSetoid) t

/-- **Selector from quotient section.**  Any section of `toWorldType` yields
a selector. -/
theorem selector_exists_of_section
    (f : S.WorldType → World) (hf : ∀ t, S.toWorldType (f t) = t) :
    Nonempty (Selector S) :=
  selector_of_lift S f hf

/-- **Selector existence (classical).**  Under classical Choice, a selector
exists for any observational semantics (section of the quotient). This is
*not* the audit theorem: selector existence does not require non-invariance.
The real audit content is `not_invariant_implies_not_decidable_on_world_type`. -/
theorem selector_exists_classical : Nonempty (Selector S) := by
  let f (t : S.WorldType) : World := Classical.choose (exists_rep S t)
  have hf : ∀ t, S.toWorldType (f t) = t := fun t =>
    (Classical.choose_spec (exists_rep S t))
  exact selector_exists_of_section S f hf

/-! ## Internal outsourcing (internal symmetry-breaking)

The *nailed* theorem: internal decider for a non-invariant property implies
**internal symmetry-breaking** (an internal selector or canonicalization). This
requires effective presentation or canonicalization assumptions; see
`Closure.Core.Canonicalization` for a concrete path. The typeclass below
states the property; nontrivial instances come from computability or
definability under those assumptions. -/

section InternalOutsourcing

variable [InternalPred (World → Bool)] [InternalPred (S.WorldType → World)]

/-- **Bridge for internal outsourcing.**  A semantics has this when: whenever
a non-invariant predicate has an **internal** total decider, some selector is
internal (internal symmetry-breaking). Nontrivial instances require effective
presentation (e.g. `EffectiveSemantics`) or canonicalization; see
`Closure.Core.Canonicalization` and `Closure.Core.Effective`. -/
class DeciderImpliesInternalSelector (S : ObsSemantics World Obs)
    [InternalPred (World → Bool)] [InternalPred (S.WorldType → World)] : Prop where
  impl :
    ∀ (P : World → Prop) (δ : World → Bool),
      TotalDecider P δ → ¬ S.Invariant P → InternalPred.Internal δ →
      ∃ sel : Selector S, SelectorInternal S sel

/-- **Internal outsourcing (internal symmetry-breaking).**  Under
`DeciderImpliesInternalSelector` (e.g. from effective semantics or internal
canonicalization), an internal total decider for a non-invariant P yields
an internal selector. -/
theorem noninvariant_decidable_implies_internal_selector
    [inst : DeciderImpliesInternalSelector S]
    (P : World → Prop) (δ : World → Bool)
    (hDec : TotalDecider P δ) (hNoninv : ¬ S.Invariant P)
    (hInternal : InternalPred.Internal δ) :
    ∃ sel : Selector S, SelectorInternal S sel :=
  inst.impl P δ hDec hNoninv hInternal

end InternalOutsourcing

end Closure
