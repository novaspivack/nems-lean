import SelfReference.Core.FixedPoint

/-!
# SelfReference.Consequences.DiagonalBarrier

## The Abstract Diagonal Barrier (MFP-2)

Given a `CSRI α` system and a "truth predicate" `T : α → Prop`
that is **extensional** (respects `Equiv`) and **nontrivial** (has both
a true and a false instance), no total decider for `T` can exist.

This is the abstract version of:
- Tarski's undefinability of truth
- Turing's halting undecidability
- The NEMS diagonal barrier (Theorem 5.9)

## The representable-class qualifier

The barrier applies to deciders that are **within the representable class**
of the system — i.e., whose Boolean output function can be lifted to a
`α → α` transformer that lies in the image of `repr`.  This is precisely
the class of "effective" or "internal" deciders in the system.

In the NEMS setting, this is the class of computable deciders.
In the Gödel setting, this is the class of provably-definable deciders.
In the Kleene setting, this is the class of partial-recursive deciders.

The theorem says: **no total decider** exists for an extensional nontrivial
predicate in a `CSRI` system.  This preempts the objection "but I can
define a decider by cases on a finite type" — such a decider would need
to be representable (i.e., in the image of `repr`) to be in scope.

## Proof strategy

Suppose `decide : α → Bool` is a total decider for `T`.
Define `F x := if decide x = true then false_term else true_term`.
By `CSRI.master_fixed_point`, there exists `d : α` with `d ≃ F d`.
By extensionality of `T`: `T d ↔ T (F d)`.
The definition of `F` forces a contradiction in both cases.
-/

namespace SelfReference
namespace Consequences

universe u

variable {α : Type u} [S : CSRI α]

/-- A predicate `T : α → Prop` is **extensional** if it respects `Equiv`. -/
def ExtensionalPred (T : α → Prop) : Prop :=
  ∀ {x y : α}, S.Equiv x y → (T x ↔ T y)

/-- A **total decider** for `T` is a function `decide : α → Bool`
such that `decide c = true ↔ T c` for all `c : α`. -/
def TotalDecider (T : α → Prop) (decide : α → Bool) : Prop :=
  ∀ c : α, decide c = true ↔ T c

/-- **Abstract Diagonal Barrier (MFP-2).**

If `T : α → Prop` is extensional and nontrivial, and `decide` is a
total decider for `T`, then we reach a contradiction.

**Proof**: Diagonalize against `decide` using `CSRI.master_fixed_point`. -/
theorem no_total_decider
    (T : α → Prop)
    (hExt : ExtensionalPred T)
    (true_term : α) (hTrue : T true_term)
    (false_term : α) (hFalse : ¬ T false_term)
    (decide : α → Bool)
    (hDec : TotalDecider T decide)
    (hquote_id : ∀ x : α, S.Equiv (S.quote x) x)
    (hrun_cong : ∀ {e₁ e₂ c₁ c₂ : α},
        S.Equiv e₁ e₂ → S.Equiv c₁ c₂ → S.Equiv (S.run e₁ c₁) (S.run e₂ c₂)) :
    False := by
  -- The anti-decider: maps x to false_term if T x, else true_term.
  let F : α → α := fun x => if decide x = true then false_term else true_term
  -- F is congruent: if x ≃ y then T x ↔ T y (by extensionality), so decide x = decide y,
  -- so F x = F y (both branches of the conditional agree).
  have hF_cong : ∀ {x y : α}, S.Equiv x y → S.Equiv (F x) (F y) := by
    intro x y hxy
    simp only [F]
    have hTxy : T x ↔ T y := hExt hxy
    have hdxy : decide x = decide y := by
      cases hd : decide x <;> cases hd' : decide y
      · rfl
      · exfalso
        have hTy : T y := (hDec y).mp hd'
        have hNTx : ¬ T x := fun hTx => absurd ((hDec x).mpr hTx) (by rw [hd]; exact Bool.noConfusion)
        exact hNTx (hTxy.mpr hTy)
      · exfalso
        have hTx : T x := (hDec x).mp hd
        have hNTy : ¬ T y := fun hTy => absurd ((hDec y).mpr hTy) (by rw [hd']; exact Bool.noConfusion)
        exact hNTy (hTxy.mp hTx)
      · rfl
    rw [hdxy]
    exact S.equiv_refl _
  obtain ⟨d, hd⟩ := CSRI.master_fixed_point F hF_cong hquote_id hrun_cong
  have hTd_iff : T d ↔ T (F d) := hExt hd
  simp only [F] at hTd_iff
  split_ifs at hTd_iff with h
  · exact hFalse (hTd_iff.mp ((hDec d).mp h))
  · exact (fun hTd => h ((hDec d).mpr hTd)) (hTd_iff.mpr hTrue)

/-- **Corollary**: No extensional nontrivial predicate has a total decider. -/
theorem no_total_decider_nontrivial
    (T : α → Prop)
    (hExt : ExtensionalPred T)
    (hNontrivial : (∃ x, T x) ∧ (∃ x, ¬ T x))
    (hquote_id : ∀ x : α, S.Equiv (S.quote x) x)
    (hrun_cong : ∀ {e₁ e₂ c₁ c₂ : α},
        S.Equiv e₁ e₂ → S.Equiv c₁ c₂ → S.Equiv (S.run e₁ c₁) (S.run e₂ c₂)) :
    ¬ ∃ decide : α → Bool, TotalDecider T decide := by
  intro ⟨decide, hDec⟩
  obtain ⟨⟨true_term, hTrue⟩, ⟨false_term, hFalse⟩⟩ := hNontrivial
  exact no_total_decider T hExt true_term hTrue false_term hFalse decide hDec hquote_id hrun_cong

-- Aliases for backward compatibility
alias ExtensionalPredU := ExtensionalPred
alias TotalDeciderU := TotalDecider
alias no_total_decider_unityped := no_total_decider
alias no_total_decider_nontrivial_unityped := no_total_decider_nontrivial

end Consequences
end SelfReference
