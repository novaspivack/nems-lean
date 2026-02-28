import NemS.Core.Basics

/-!
# NemS.Core.ObsEq

Record observational equivalence: two models are observationally equivalent
if they agree on the truth-value of every record statement.

We prove this is an equivalence relation and package it as a `Setoid`
so Lean's quotient machinery applies cleanly.
-/


namespace NemS

variable {u v : Universe}

namespace Framework

variable (F : Framework)

/-- Two models are *record observationally equivalent* if they agree on
every record statement in `F.Rec`. -/
def ObsEq (M N : F.Model) : Prop :=
  ∀ r : F.Rec, F.Truth M r ↔ F.Truth N r

namespace ObsEq

variable {F : Framework}

@[refl]
theorem refl (M : F.Model) : F.ObsEq M M :=
  fun _ => Iff.rfl

@[symm]
theorem symm {M N : F.Model} (h : F.ObsEq M N) : F.ObsEq N M :=
  fun r => (h r).symm

@[trans]
theorem trans {M N P : F.Model} (h₁ : F.ObsEq M N) (h₂ : F.ObsEq N P) :
    F.ObsEq M P :=
  fun r => (h₁ r).trans (h₂ r)

/-- `ObsEq` is an equivalence relation. -/
theorem isEquivalence : Equivalence F.ObsEq :=
  ⟨refl, symm, trans⟩

end ObsEq

/-- Package `ObsEq` as a `Setoid` on `F.Model` so we can form quotients. -/
def obsEqSetoid : Setoid F.Model where
  r     := F.ObsEq
  iseqv := ObsEq.isEquivalence

/-- The set of *observational world-types*: the quotient of models by
record observational equivalence.  This is `WTypes(T; L_rec)` in the paper. -/
def WorldTypes : Type _ := Quotient F.obsEqSetoid

/-- Canonical map sending a model to its observational equivalence class. -/
def toWorldType (M : F.Model) : F.WorldTypes :=
  Quotient.mk F.obsEqSetoid M

/-- Two models map to the same world-type iff they are observationally
equivalent. -/
theorem toWorldType_eq_iff {M N : F.Model} :
    F.toWorldType M = F.toWorldType N ↔ F.ObsEq M N :=
  Quotient.eq (r := F.obsEqSetoid)

end Framework

end NemS
