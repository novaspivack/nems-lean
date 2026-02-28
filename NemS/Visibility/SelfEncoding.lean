import NemS.Visibility.Recordability

/-!
# NemS.Visibility.SelfEncoding

The *self-encoding extension* `F⁺` of a framework `F` with evaluator type `E`
extends the record statements to include "evaluator trace" facts.

- `Rec⁺ := F.Rec ⊕ E`
- `Truth⁺ (M, e) (inl r) := F.Truth M r`
- `Truth⁺ (M, e) (inr e') := (e = e')`
-/

namespace NemS

namespace Framework

variable (F : Framework)

def selfEncode (E : Type) : Framework where
  Model := F.Model × E
  Rec   := F.Rec ⊕ E
  Truth := fun ⟨M, e⟩ stmt =>
    match stmt with
    | Sum.inl r  => F.Truth M r
    | Sum.inr e' => e = e'

namespace SelfEncoding

variable {F : Framework} (E : Type)

theorem conservative (M : F.Model) (e : E) (r : F.Rec) :
    (F.selfEncode E).Truth ⟨M, e⟩ (Sum.inl r) ↔ F.Truth M r :=
  Iff.rfl

theorem trace_truth (M : F.Model) (e e' : E) :
    (F.selfEncode E).Truth ⟨M, e⟩ (Sum.inr e') ↔ e = e' :=
  Iff.rfl

/-- Two pairs `(M, e₁)` and `(M, e₂)` with `e₁ ≠ e₂` are not
observationally equivalent in `F⁺`. -/
theorem distinct_evaluators_not_obsEq
    {M : F.Model} {e₁ e₂ : E} (hne : e₁ ≠ e₂) :
    ¬ (∀ r : F.Rec ⊕ E,
        (F.selfEncode E).Truth ⟨M, e₁⟩ r ↔ (F.selfEncode E).Truth ⟨M, e₂⟩ r) := by
  intro h
  -- (h (Sum.inr e₁)).mp rfl : (F.selfEncode E).Truth ⟨M, e₂⟩ (Sum.inr e₁)
  -- which unfolds to e₂ = e₁; we need e₁ ≠ e₂, so use .symm
  have h21 : (F.selfEncode E).Truth ⟨M, e₂⟩ (Sum.inr e₁) := (h (Sum.inr e₁)).mp rfl
  -- h21 : e₂ = e₁
  exact hne h21.symm

end SelfEncoding

end Framework

end NemS
