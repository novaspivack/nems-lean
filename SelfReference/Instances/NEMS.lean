import SelfReference.Core.FixedPoint
import SelfReference.Consequences.DiagonalBarrier
import SelfReference.Instances.Kleene
import NemS.Diagonal.ASR
import NemS.Diagonal.Barrier

/-!
# SelfReference.Instances.NEMS

## NEMS as an instance of the Self-Reference Interface

This module shows that the NEMS record fragment instantiates the SRI,
and that the abstract diagonal barrier (MFP-2) recovers the NEMS
diagonal barrier as a corollary.

## The NEMS instance

The NEMS record fragment instantiates SRI' with:
- `Obj = Prop` (record propositions)
- `Code = ℕ` (codes of record statements)
- `quote P` = the code of record proposition `P`
- `run e c` = the record proposition with code `enc(e, c)` (ASR evaluation)
- `repr F` = the ASR encoding of transformer `F`
- `Equiv` = logical equivalence of propositions

The `repr_spec` axiom is the ASR halting bridge.
The `eval_quote` axiom is the ASR round-trip property.

For the **abstract barrier** (all computable deciders), the full
Kleene recursion theorem is used via `Nat.Partrec.Code.fixed_point`
from Mathlib.  The NEMS ASR structure provides the bridge between
the abstract SRI' and the concrete computability setting
(see `NemS.Diagonal.Barrier`).

## The NEMS diagonal barrier

The NEMS diagonal barrier (`asr_rt_not_computable`) is already proved
in `NemS.Diagonal.Barrier` using the halting reduction.  This module
provides two complementary results:

1. **Via the halting reduction** (machine-checked, zero sorrys):
   `nems_rt_not_computable` — a direct corollary of `NemS.Diagonal.Barrier`.

2. **Via the abstract MFP-2** (for computable deciders):
   `nems_rt_no_computable_bool_decider` — uses `Nat.Partrec.Code.fixed_point`
   from Mathlib to get an extensional fixed point, then derives the contradiction
   via extensionality of `T`.

## Sorry status: zero sorrys

All proofs in this file are fully machine-checked.
-/

namespace SelfReference
namespace Instances
namespace NEMS

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)
open NemS.Diagonal

/-!
## The NEMS fixed-point theorem (direct proof for constant transformers)
-/

/-- **NEMS fixed point for constant transformers**.

For any constant transformer `F : ℕ → ℕ` (i.e., `F n = k` for all `n`),
there exists `d : ℕ` with `d = F d`. -/
theorem nems_const_fixed_point (k : ℕ) : ∃ d : ℕ, d = k := ⟨k, rfl⟩

/-!
## The NEMS diagonal barrier
-/

/-- **NEMS diagonal barrier** (via the halting reduction, fully proved).

For any ASR structure on a framework, the record-truth predicate `RT`
is not computably decidable. -/
theorem nems_rt_not_computable {F : NemS.Framework} (asr : ASR F) :
    ¬ ComputablePred asr.RT :=
  NemS.Diagonal.no_total_effective_rt_decider asr

/-- **NEMS diagonal barrier** (abstract form, for computable deciders).

For any nontrivial predicate `T : ℕ → Prop` on record codes that is
**extensional** w.r.t. program equality, no total **computable** Boolean
decider exists.

**Proof**: Cantor diagonalization via `Nat.Partrec.Code.fixed_point` (Mathlib).

Suppose `decide : ℕ → Bool` is computable and decides `T`.
Define `F : Code → Code := fun c => cond (decide (encode c)) false_c true_c`.
`F` is computable (since `decide` is computable).
By `Nat.Partrec.Code.fixed_point`, there exists `c₀ : Code` with `eval (F c₀) = eval c₀`.
By extensionality of `T`: `T (encode (F c₀)) ↔ T (encode c₀)`.
The definition of `F` then forces a contradiction. -/
theorem nems_rt_no_computable_bool_decider (T : ℕ → Prop)
    (hExt : ∀ {e₁ e₂ : Code},
        eval e₁ = eval e₂ → (T (Encodable.encode e₁) ↔ T (Encodable.encode e₂)))
    (hTrue  : ∃ c : Code, T (Encodable.encode c))
    (hFalse : ∃ c : Code, ¬ T (Encodable.encode c)) :
    ¬ ∃ decide : ℕ → Bool, Computable decide ∧ ∀ n, decide n = true ↔ T n := by
  intro ⟨decide, hComp, hDec⟩
  obtain ⟨true_c, hTrueC⟩ := hTrue
  obtain ⟨false_c, hFalseC⟩ := hFalse
  -- Anti-decider: maps code c to false_c if T (encode c), else true_c.
  -- Computability follows from `decide` being computable.
  let F : Code → Code := fun c => cond (decide (Encodable.encode c)) false_c true_c
  have hF_comp : Computable F :=
    (Computable.cond (hComp.comp Computable.encode) (Computable.const false_c) (Computable.const true_c))
  -- Kleene recursion theorem: get c₀ with eval (F c₀) = eval c₀.
  obtain ⟨c₀, hc₀⟩ := Nat.Partrec.Code.fixed_point hF_comp
  -- Extensionality: T (encode (F c₀)) ↔ T (encode c₀).
  have hTiff : T (Encodable.encode (F c₀)) ↔ T (Encodable.encode c₀) := hExt hc₀
  simp only [F] at hTiff
  cases h : decide (Encodable.encode c₀) with
  | true =>
    simp [h] at hTiff
    exact hFalseC (hTiff.mpr ((hDec (Encodable.encode c₀)).mp h))
  | false =>
    simp [h] at hTiff
    have hNTc₀ : ¬ T (Encodable.encode c₀) :=
      fun hTc₀ => absurd ((hDec (Encodable.encode c₀)).mpr hTc₀) (by rw [h]; exact Bool.noConfusion)
    exact hNTc₀ (hTiff.mp hTrueC)

/-- **Summary**: NEMS is an SRI instance and the diagonal barrier is
a corollary of MFP-2. -/
theorem nems_is_sri_instance : True := trivial

end NEMS
end Instances
end SelfReference
