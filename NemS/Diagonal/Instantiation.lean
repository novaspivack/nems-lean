import NemS.Diagonal.Barrier

/-!
# NemS.Diagonal.Instantiation

A concrete ASR instantiation using Mathlib's `Nat.Partrec.Code` and
`eval`, demonstrating that the ASR structure is satisfiable.

## The halting framework

We construct a framework where:
- `Model := ℕ` (natural numbers index programs via Gödel coding)
- `Rec := ℕ` (natural numbers index record statements)
- `Truth m r` holds iff the program coded by `m` halts on input `r`

## The ASR structure

Uses `Denumerable Code` to go between `Code` and `ℕ`:
- `RT n` decodes `n` as a pair `(code_index, input)` and checks halting
- `encode c x := Nat.pair (Encodable.encode c) x`
- The bridge `halts_iff_RT` holds by the round-trip property of `Denumerable`

## Consistency check

We apply `no_total_effective_rt_decider` to this instantiation,
recovering the undecidability of halting as a corollary.
-/

namespace NemS
namespace Diagonal

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

/-- The halting framework: natural numbers (as Gödel codes of programs)
are models, halting is truth. -/
def haltingFramework : Framework where
  Model := ℕ
  Rec := ℕ
  Truth := fun m r => (eval (Denumerable.ofNat Code m) r).Dom

/-- The ASR structure for the halting framework.

Uses `Denumerable Code` for the encoding/decoding round-trip. -/
noncomputable def haltingASR : ASR haltingFramework where
  RT := fun n => (eval (Denumerable.ofNat Code n.unpair.1) n.unpair.2).Dom
  encode := fun c x => Nat.pair (Encodable.encode c) x
  encode_computable :=
    Computable.pair
      (Computable.encode.comp Computable.fst)
      Computable.snd
  halts_iff_RT := fun c x => by
    simp only [Nat.unpair_pair]
    rw [Denumerable.ofNat_encode c]

/-- Consistency check: the diagonal barrier on the halting framework
recovers the undecidability of halting. -/
theorem halting_framework_rt_not_computable :
    ¬ ComputablePred haltingASR.RT :=
  no_total_effective_rt_decider haltingASR

end Diagonal
end NemS
