import NemS.Core.Basics

/-!
# NemS.Physical.UniversalComputation

Physical Universal Computation (PhysUCT) capability for frameworks.

This module defines a minimal interface capturing the physical capability
to implement universal computation with stable records.  The key content:
a framework has PhysUCT if its record fragment can encode the execution
of a universal machine and its halting behavior.

This is weaker than full ASR (which requires the encoding to be computable
and provides the full halting bridge).  PhysUCT is the "physically motivated"
premise: "computers exist and their behavior is record-expressible."

The main result (in `ASRFromUCT.lean`) will be: PhysUCT ⇒ DiagonalCapable
(ASR can be constructed from PhysUCT).
-/

namespace NemS
namespace Physical

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

/-- A framework has *Physical Universal Computation* (PhysUCT) capability
if its record fragment can express the halting behavior of a universal
computational substrate.

Concretely, this requires:
- A record-truth predicate RT on coded statements
- A computable encoding from program codes and inputs to codes
- A bridge showing halting ↔ RT on the encoding

This is the "physically motivated" premise: "the universe can host
universal computation, and whether a computation halts is a physically
meaningful, record-expressible fact."

PhysUCT is essentially ASR stated in physical terms.  The distinction
is pedagogical: PhysUCT emphasizes the physical motivation
("computers exist"), while ASR emphasizes the formal diagonal-capability
consequence. -/
structure PhysUCT (F : Framework) where
  /-- Record-truth predicate on coded record statements. -/
  RT : ℕ → Prop
  /-- Computable encoding from (program code, input) to record-statement code. -/
  encode : Code → ℕ → ℕ
  /-- The encoding is computable. -/
  encode_computable : Computable₂ encode
  /-- Halting bridge: halting ↔ record-truth on the encoding. -/
  halts_iff_RT : ∀ (c : Code) (x : ℕ), (eval c x).Dom ↔ RT (encode c x)

end Physical
end NemS
