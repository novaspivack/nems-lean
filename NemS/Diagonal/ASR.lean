import NemS.Core.Basics
import NemS.Core.ObsEq
import NemS.Core.Categoricity
import NemS.Core.Selectors

/-!
# NemS.Diagonal.ASR

Arithmetic Self-Reference (ASR) package for the diagonal barrier.

An ASR structure on a framework `F` witnesses that the record fragment
is expressive enough to encode the halting problem.  Concretely, it
provides:
- A *record-truth* function `RT : ℕ → Prop` that captures the
  truth-values of coded record statements.
- A bridge showing that `RT` is at least as hard as the halting problem:
  any total computable decider for `RT` would yield a total computable
  decider for halting.

This is the Lean formalization of ASR conditions (ii)–(iv) from
Section 5 of the NEMS theorem paper.
-/

namespace NemS
namespace Diagonal

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

/-- An `ASR` (Arithmetic Self-Reference) structure on a framework `F`
witnesses that the record fragment can encode halting.

- `RT` is the "record-truth on codes" function: `RT n` means
  coded record statement `n` is true in the realized world.
- `encode` maps a program code and input to a record-statement code.
- `halts_iff_RT` bridges halting to record-truth: program `c` halts
  on input `x` iff `RT (encode c x)` holds.

The existence of such a structure means the record fragment is
"diagonal-capable": it can express enough about computation to
trigger undecidability arguments. -/
structure ASR (F : Framework) where
  /-- Record-truth on codes: which coded record statements are true. -/
  RT : ℕ → Prop
  /-- Encoding: maps a program code and input to a record-statement code. -/
  encode : Code → ℕ → ℕ
  /-- The encoding is computable (total, primitive recursive). -/
  encode_computable : Computable₂ encode
  /-- Bridge: halting ↔ record-truth on the encoded statement. -/
  halts_iff_RT : ∀ (c : Code) (x : ℕ), (eval c x).Dom ↔ RT (encode c x)

end Diagonal
end NemS
