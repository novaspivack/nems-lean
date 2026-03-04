import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import SelectorStrength.Theorems.BarrierSchema

/-!
# SelectorStrength.Instances.Trivial

**Trivial strength: all functions (Paper 29).**

S_all f := True. This is the top strength (every function is in the class).
Anti-decider closure holds trivially. S_all alone does *not* imply "no
deciders"; the barrier still requires a global fixed-point premise (hFP).
Under that premise (e.g. from CSRI / MFP-1), the barrier schema yields: no
total decider for extensional nontrivial T — recovering the raw logical
barrier (MFP-2).
-/

set_option autoImplicit false

namespace SelectorStrength

universe u

variable {α : Type u}

/-- **Trivial strength (all functions)**: every function is in the class. -/
def S_all : Strength α Bool := fun _ => True

/-- **Trivial strength for transformers**. -/
def S_all_α : Strength α α := fun _ => True

/-- S_all is anti-decider closed: the anti-decider is a function, hence in S_all_α. -/
theorem antiDeciderClosed_all : AntiDeciderClosed (α := α) S_all S_all_α :=
  fun _ _ _ _ => trivial

/-- When hFP holds for all F (e.g. from CSRI/master_fixed_point), the barrier
schema applies: no total decider in S_all for extensional nontrivial T.
(DecidableAt S_all T would mean *some* total decider exists; the barrier
shows none can exist when hFP holds for the anti-decider.) -/
theorem no_total_decider_all
    (Equiv : α → α → Prop)
    (T : α → Prop)
    (hExt : Extensional Equiv T)
    (hNontriv : Nontrivial T)
    (hFP : ∀ F : α → α, ∃ d : α, Equiv d (F d)) :
    ¬ DecidableAt S_all T :=
  no_total_decider_at_strength_nontrivial Equiv T hExt hNontriv S_all S_all_α
    (antiDeciderClosed_all (α := α)) (fun F _ => hFP F)

end SelectorStrength
