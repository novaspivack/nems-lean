import NemS.Prelude
import Closure.Core.ObsSemantics

/-!
# ChronologyUnderClosure.Core.RecordDynamics

**Paper 36: Record dynamics and feedback (time-travel) operator.**

Worlds are interpreted as histories; a feedback map F represents the
"next step" or closed-timelike evolution. Self-consistent loop = fixed point
modulo observational equivalence.
-/

set_option autoImplicit false

namespace ChronologyUnderClosure

universe u v

variable {World : Type u} {Obs : Type v} (S : Closure.ObsSemantics World Obs)

/-- A **feedback operator** on worlds (histories): one step of "time-travel" or CTC evolution. -/
def Feedback (World : Type u) : Type u := World → World

variable (F : Feedback World)

/-- **Self-consistent loop**: world `w` is a fixed point modulo observational equivalence,
i.e. `F w` is observationally equivalent to `w` (Deutsch/Novikov self-consistency). -/
def SelfConsistent (w : World) : Prop :=
  S.ObsEquiv (F w) w

/-- **Overwrite**: at world `w`, observational proposition `o` holds but does not hold at `F w`.
So the feedback "overwrites" the record given by `o`. -/
def Overwrite (w : World) (o : Obs) : Prop :=
  S.Holds w o ∧ ¬ S.Holds (F w) o

end ChronologyUnderClosure
