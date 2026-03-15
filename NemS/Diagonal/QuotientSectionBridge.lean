import Mathlib.Computability.Halting
import NemS.Core.QuotientSection
import NemS.Diagonal.Instantiation
import NemS.Diagonal.ASR

/-!
# NemS.Diagonal.QuotientSectionBridge

Bridge from the diagonal barrier (ASR) to the quotient-section realizability theorem.

Proves that the halting framework has no computably realizable quotient section:
a concrete instantiation of `no_total_effective_quotient_section_on_diagonal_fragment`.
-/

namespace NemS
namespace Diagonal

open Encodable Denumerable
open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)
open NemS.Framework

/-- For each `k`, the partial function χₖ(x) = 0 if x = k else undefined is partial recursive. -/
theorem partrec_singleton_halting (k : ℕ) :
    Nat.Partrec (fun x => if x = k then Part.some 0 else Part.none) := by
  have hk : Computable fun x : ℕ => (x == k : Bool) :=
    (Primrec.beq.comp Primrec.id (Primrec.const k)).to_comp
  have h := Partrec.cond hk (Partrec.nat_iff.2 Nat.Partrec.zero) Partrec.none
  exact Partrec.nat_iff.1 (h.of_eq fun n => by
    simp only [Bool.cond_eq_ite, beq_iff_eq]; congr 1)

/-- The halting framework has unboundedly many world-types: for each `n`, there
exist at least `n + 1` pairwise observationally distinct models (programs with
distinct halting sets).

Proof: For each k ≤ n, the partial function χₖ(x) = 0 if x = k else undefined
is partial recursive, hence (by `Nat.Partrec.Code.exists_code`) has a code cₖ.
These codes have distinct halting sets, so the corresponding model indices
(via `Denumerable.ofNat Code`) are pairwise not ObsEq. -/
theorem halting_framework_unbounded_world_types :
    UnboundedWorldTypes haltingFramework := by
  intro n
  -- For each i : Fin (n+1), obtain a code cᵢ whose halting set is exactly {i.val}
  let m (i : Fin (n + 1)) : ℕ :=
    Encodable.encode (Classical.choose (Code.exists_code.1 (partrec_singleton_halting i.val)))
  use m
  intro i j hne
  -- m i and m j decode to codes with halting sets {i.val} and {j.val} respectively
  let ci := Classical.choose (Code.exists_code.1 (partrec_singleton_halting i.val))
  let cj := Classical.choose (Code.exists_code.1 (partrec_singleton_halting j.val))
  have ei : eval ci = fun x => if x = i.val then Part.some 0 else Part.none :=
    Classical.choose_spec (Code.exists_code.1 (partrec_singleton_halting i.val))
  have ej : eval cj = fun x => if x = j.val then Part.some 0 else Part.none :=
    Classical.choose_spec (Code.exists_code.1 (partrec_singleton_halting j.val))
  have encode_ci : ofNat Code (Encodable.encode ci) = ci := Denumerable.ofNat_encode ci
  have encode_cj : ofNat Code (Encodable.encode cj) = cj := Denumerable.ofNat_encode cj
  have hDomI : (eval ci i.val).Dom := by
    show (eval ci i.val).Dom
    rw [show eval ci i.val = (fun x => if x = i.val then Part.some 0 else Part.none) i.val
        from congr_fun ei i.val]
    simp
  have hNotDomJ : ¬(eval cj i.val).Dom := by
    rw [show eval cj i.val = (fun x => if x = j.val then Part.some 0 else Part.none) i.val
        from congr_fun ej i.val]
    simp [show ¬(i.val = j.val) from mt Fin.val_inj.mp hne]
  intro hObsEq
  have hEq := hObsEq i.val
  simp only [haltingFramework] at hEq
  rw [encode_ci, encode_cj] at hEq
  exact hNotDomJ (hEq.1 hDomI)

/-- **Halting framework: no computably realizable quotient section (Target E bridge).**

The halting framework has ASR and unbounded world-types. By
`no_total_effective_quotient_section_on_diagonal_fragment`, no quotient section
can be computably realized. -/
theorem halting_framework_no_computable_section
    (q : haltingFramework.WorldTypes → ℕ)
    (_hsec : IsQuotientSection haltingFramework q) :
    ¬ IsComputablyRealizedSection q :=
  no_total_effective_quotient_section_on_diagonal_fragment
    haltingASR halting_framework_unbounded_world_types q _hsec

end Diagonal
end NemS
