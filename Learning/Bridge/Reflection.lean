import Reflection.Core.SRI_R
import Reflection.Theorems.DiagonalClosure
import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import Learning.Theorems.SelfTrustBarrier

/-!
# Learning.Bridge.Reflection

**Reflection supplies the fixed-point premise for the self-trust barrier (Paper 30 + 28).**

When the certificate type `Cert` carries an SRI_R with a diagonally closed R, and
quote is the identity (unityped / codes-as-objects), Reflection's
`restricted_master_fixed_point` yields the hFP premise required by the barrier:
every F in R has a fixed point d with Equiv d (F d). We package this so the
self-trust barrier can be instantiated from Reflection.
-/

set_option autoImplicit false

namespace Learning

universe u

variable {Cert : Type u} {R : (Cert → Cert) → Prop} [sri : Reflection.SRI_R Cert Cert R]

/-- When `quote` is the identity, the Reflection mixed fixed point
`p ≃ F(quote p)` becomes `p ≃ F p`, which is the shape required by the
barrier's hFP. -/
theorem reflection_supplies_hFP_for_learning
    (hDiag : Reflection.DiagClosed R)
    (hQuoteId : ∀ c : Cert, sri.quote c = c)
    (F : Cert → Cert) (hF : R F) :
    ∃ d : Cert, sri.Equiv d (F d) := by
  obtain ⟨p, hp⟩ := Reflection.restricted_master_fixed_point hDiag F hF
  use p
  rw [hQuoteId p] at hp
  exact hp

/-- **Barrier premise from Reflection**: when R is diagonally closed and
quote = id, the fixed-point premise hFP holds for all F ∈ R. This allows
applying `no_total_self_certifier` when the strength corresponds to R. -/
theorem barrier_premise_from_reflection
    (hDiag : Reflection.DiagClosed R)
    (hQuoteId : ∀ c : Cert, sri.quote c = c) :
    ∀ F : Cert → Cert, R F → ∃ d : Cert, sri.Equiv d (F d) :=
  fun F hF => reflection_supplies_hFP_for_learning hDiag hQuoteId F hF

end Learning
