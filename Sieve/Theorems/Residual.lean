import NemS.Prelude
import Mathlib.Data.List.Basic
import Sieve.Core.Constraints

/-!
# Sieve.Theorems.Residual

**Monotonicity and pullback (Paper 34).**

- Adding constraints shrinks the residual: if cs' ⊇ cs (as constraint set),
  then every element of Residual cs' is in Residual cs.
- Residual functoriality: pullback of constraints along a map preserves sieve membership
  (sieve analogue of interpretation preservation from Closure).
-/

set_option autoImplicit false

namespace Sieve

variable {α β : Type _}

private theorem forall_mem {α : Type _} {a : α} {l : List α} {p : α → Prop}
    (h : l.Forall p) (hm : a ∈ l) : p a := by
  induction l with
  | nil => cases hm
  | cons b l ih =>
    simp only [List.forall_cons, List.mem_cons] at h hm
    cases hm with
    | inl heq => rw [heq]; exact h.1
    | inr hm' => exact ih h.2 hm'

private theorem sublist_mem {α : Type _} {l₁ l₂ : List α} {a : α}
    (h : l₁.Sublist l₂) (ha : a ∈ l₁) : a ∈ l₂ := by
  induction h with
  | slnil => cases ha
  | cons _ hsub ih => exact List.mem_cons_of_mem _ (ih ha)
  | cons₂ _ hsub ih => cases ha with
    | head => exact List.mem_cons_self
    | tail _ hb => exact List.mem_cons_of_mem _ (ih hb)

private theorem sublist_tail {α : Type _} {a : α} {l₁ l₂ : List α}
    (h : (a :: l₁).Sublist l₂) : l₁.Sublist l₂ := by
  cases h with
  | cons a' hsub => exact List.Sublist.cons a' (sublist_tail hsub)
  | cons₂ _ hsub => exact List.Sublist.cons a hsub

/-- If cs is a sublist of cs', then any candidate satisfying the sieve of cs'
also satisfies the sieve of cs. (Adding constraints shrinks the residual.) -/
theorem sieve_sublist (cs cs' : List (Constraint α)) (a : α)
    (h : cs.Sublist cs') (ha : SieveHolds α cs' a) :
    SieveHolds α cs a := by
  unfold SieveHolds at *
  induction cs generalizing cs' with
  | nil => trivial
  | cons C cs ih =>
    simp only [List.forall_cons] at ⊢
    have hCmem : C ∈ cs' := sublist_mem h (by simp only [List.mem_cons]; left; trivial)
    have hC : C a := forall_mem (p := fun x => x a) ha hCmem
    exact ⟨hC, ih cs' (sublist_tail h) ha⟩

/-- Monotonicity of residual: if cs is a sublist of cs', then any candidate
in Residual α cs' (satisfying the larger sieve) also satisfies the smaller sieve. -/
theorem residual_mono (cs cs' : List (Constraint α)) (a : α)
    (hsub : cs.Sublist cs') (ha : SieveHolds α cs' a) :
    SieveHolds α cs a :=
  sieve_sublist cs cs' a hsub ha

/-- Pullback of a constraint list along a map: constraints on β become constraints on α
via precomposition with f. -/
def pullbackConstraints (f : α → β) (ds : List (Constraint β)) : List (Constraint α) :=
  ds.map (fun D a => D (f a))

/-- Residual functoriality: a satisfies the pullback sieve (on α) iff f a satisfies
the sieve on β. (Sieve analogue of interpretation preservation from Closure.) -/
theorem sieve_pullback (f : α → β) (ds : List (Constraint β)) (a : α) :
    SieveHolds α (pullbackConstraints f ds) a ↔ SieveHolds β ds (f a) := by
  unfold pullbackConstraints SieveHolds
  simp only [List.forall_map_iff]
  exact Iff.rfl

end Sieve
