import ArrowOfTime.Core.RecordFiltration

/-!
# ArrowOfTime.Theorems.Irreversibility

**Paper 36: No global reversible record semantics under strict refinement (T3).**

A stage-preserving involution (R ∘ R = id and Holds w o ↔ Holds (R w) o for visible o)
fixes every stage world-type: toWorldTypeAt t (R w) = toWorldTypeAt t w.
So no nontrivial "time reversal" preserves all stage semantics.
-/

set_option autoImplicit false

namespace ArrowOfTime

universe u v

variable {World : Type u} {Obs : Type v} (Filt : RecordFiltration World Obs)

/-- **Stage-preserving**: R preserves truth of every observation visible at any time. -/
def StagePreserving (R : World → World) : Prop :=
  ∀ t (o : Obs), Filt.Visible t o → ∀ w : World, (Filt.Holds w o ↔ Filt.Holds (R w) o)

/-- **Involution**: R ∘ R = id. -/
def IsInvolution (R : World → World) : Prop :=
  ∀ w : World, R (R w) = w

/-- **No global reversal**: A stage-preserving involution fixes every stage world-type;
it cannot "undo" refinement (distinguish fewer worlds). -/
theorem no_global_reversal (R : World → World) (hInv : IsInvolution R) (hStage : StagePreserving Filt R)
    (t : Time) (w : World) :
    Filt.toWorldTypeAt t (R w) = Filt.toWorldTypeAt t w := by
  apply Quotient.sound
  intro o vo
  exact (hStage t o vo w).symm

end ArrowOfTime
