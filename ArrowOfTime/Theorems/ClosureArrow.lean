import ArrowOfTime.Core.RecordFiltration
import ArrowOfTime.Theorems.Irreversibility

/-!
# ArrowOfTime.Theorems.ClosureArrow

**Paper 36 / Paper 78: Closure Arrow Theorem (wrapper).**

Packages the existing irreversibility result as a single citation target for the
synthesis paper. Under a record filtration (stable records, refinement flow,
closure-compatible semantics), any stage-preserving involution fixes world-types:
structural irreversibility / no categoricity-preserving reversal.
-/

set_option autoImplicit false

namespace ArrowOfTime

universe u v

variable {World : Type u} {Obs : Type v} (Filt : RecordFiltration World Obs)

open ArrowOfTime.Theorems.Irreversibility

/-- **Closure Arrow Theorem.**

Under a record filtration (Paper 36), any stage-preserving involution R fixes
every stage world-type: R cannot "reverse" the arrow. This is the formal theorem
matching the synthesis-paper slogan: stable records + closure ⇒ structural irreversibility.
-/
theorem closure_arrow_theorem (R : World → World) (hInv : IsInvolution R)
    (hStage : StagePreserving Filt R) (t : Time) (w : World) :
    Filt.toWorldTypeAt t (R w) = Filt.toWorldTypeAt t w :=
  no_global_reversal Filt R hInv hStage t w

end ArrowOfTime
