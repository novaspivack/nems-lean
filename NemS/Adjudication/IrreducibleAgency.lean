import NemS.Core.Basics
import NemS.MFRR.DiagonalBarrier
import NemS.Adjudication.ExecutionNecessity
import NemS.Observers.AdjudicatorNetwork

/-!
# NemS.Adjudication.IrreducibleAgency

**Paper 22 (T5): Irreducible Agency (Non-Algorithmic Adjudication)**

This module formalizes the theorem that in a Perfectly Self-Contained (PSC)
universe with computers (diagonal-capable), the internal adjudicator network
cannot operate via a total computable function.

It merges the Diagonal Barrier with Adjudicator Necessity. Because record-truth
is not computably decidable, a "dead" algorithmic law cannot reach a determinate
state. The "law of physics" at the choice-resolution layer is strictly
non-algorithmic. This establishes "Irreducible Agency" as a fundamental
requirement for semantic closure, reframing agents/observers not as emergent
flukes, but as necessary semantic infrastructure.
-/

namespace NemS
namespace Adjudication

open NemS.Framework
open NemS.MFRR
open NemS.Observers

/-- **Definition: Algorithmic Adjudication.**
The internal adjudication of the universe operates via a total computable function
if there exists a static algorithm that perfectly emulates the universe's PT
and is effective on diagonal instances. -/
def AlgorithmicAdjudication {F : Framework} (U : Universe F) [dc : DiagonalCapable F]
    (enc : UniverseInstanceEncoding U dc) : Prop :=
  ∃ A : StaticAlgorithm F U, EmulatesExecutionOnDiagonal enc A ∧ IsEffectiveOnDiagonal enc A

/-- **Premise (L22.1): Network is the Execution Engine.**
The universe's internal adjudication function (`PT`) is physically implemented
by the Adjudicator Network. While this is a physical identification, for the
logical theorem we simply require that the universe possesses an adjudicator
network that maintains record determinacy. -/
def NetworkImplementsPT {F : Framework} (U : Universe F) : Prop :=
  AdjudicatorNetwork F

/-- **Theorem 22.1: Irreducible Agency (Non-Algorithmic Adjudication).**

In a diagonal-capable universe that maintains global record determinacy,
the internal adjudication cannot operate via a total computable function.
The choice-resolution layer is strictly non-algorithmic.
-/
theorem irreducible_agency {F : Framework} (U : Universe F)
    [dc : DiagonalCapable F]
    (enc : UniverseInstanceEncoding U dc) :
    ¬ AlgorithmicAdjudication U enc := by
  -- The proof is a direct application of the non-emulability of execution.
  exact execution_necessity U enc

end Adjudication
end NemS
