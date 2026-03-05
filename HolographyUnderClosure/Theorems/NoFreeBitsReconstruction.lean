import Closure.Theorems.AuditSoundness
import Closure.Core.ObsSemantics

/-!
# HolographyUnderClosure.Theorems.NoFreeBitsReconstruction

**Paper 48 T48.2: No-free-bits reconstruction.**

Any attempt to decide a **non-invariant** bulk predicate purely from world-types
violates Closure's audit soundness: such a decider would factor through the
quotient, so the predicate would be invariant. Therefore "extra decoding bits"
(deciding non-invariant bulk truth from boundary) are selectors unless
internalized as adjudication. We state the contrapositive: non-invariant ⇒
not decidable on world-types (Closure.audit_soundness).
-/

set_option autoImplicit false

namespace HolographyUnderClosure

universe u v

variable {World : Type u} {Obs : Type v} (S : Closure.ObsSemantics World Obs)

open Closure

/-- **T48.2 No-free-bits reconstruction (bulk side).** If a bulk predicate P is
not observationally invariant, then it is not decidable on world-types—no
reconstruction from boundary world-type data can decide P without a selector.
This is the audit soundness contrapositive (Paper 27). -/
theorem no_free_bits_reconstruction (P : World → Prop) (h : ¬ S.Invariant P) :
    ¬ Closure.DecidableOnWorldType S P :=
  Closure.not_invariant_implies_not_decidable_on_world_type S P h

end HolographyUnderClosure
