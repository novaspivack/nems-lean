import NemS.Core.Basics
import NemS.Physics.Rigidity

/-!
# NemS.Terminality.ExistentialRigidity

**Paper 21: The Theorem of Existential Rigidity (The End of Choice)**

This module formalizes the ultimate ontological conclusion of the NEMS framework:
in a self-contained reality, mathematical possibility collapses into a single
singular solution. "God had no choice."

It builds upon the Sieve Theorem (Paper 20) and the Semantic Terminality
theorem (Paper 18) to show that if the Residual Classification Conjecture holds,
the Standard Model signature is not just an optimal effective theory, but the
*only* ontologically legal foundation for a universe that avoids external
selection.
-/

namespace NemS
namespace Terminality

open NemS.Physics
open NemS.Optimality

/-- **Definition: Ontologically Legal.**
A theory is ontologically legal if it is foundational (does not require
external selectors/free bits) and is not physically redundant relative to
a PSC-optimal terminal theory. -/
def OntologicallyLegal {S : GaugeTheorySpace} (T : S.Theory) : Prop :=
  ¬ S.FailsPSC T ∧ ¬ ∃ T_base, S.PSCOptimal T_base ∧ S.Redundant T T_base

/-- **Premise (L21.1): Legality implies Admissibility.**
If a gauge theory is ontologically legal (foundational and non-redundant),
it must pass the PSC Sieve (it must be structurally stable, anomaly-free, etc.). -/
def LegalityImpliesAdmissibility (S : GaugeTheorySpace) : Prop :=
  ∀ T, OntologicallyLegal T → S.PSCAdmissible T

/-- **Theorem 21.1: Existential Rigidity.**

If the Residual Classification Conjecture holds, and if ontological legality
implies PSC admissibility, then any ontologically legal gauge theory must
possess the Standard Model signature.

Mathematical possibility collapses into a single solution.
-/
theorem existential_rigidity (S : GaugeTheorySpace)
    (h_rcc : S.ResidualClassificationConjecture)
    (h_legal_admissible : LegalityImpliesAdmissibility S)
    (T : S.Theory) (h_legal : OntologicallyLegal T) :
    S.SMSignature T := by
  -- 1. Legality implies the theory passes the PSC sieve
  have h_admissible : S.PSCAdmissible T := h_legal_admissible T h_legal
  -- 2. By Paper 20's gauge signature rigidity, an admissible theory has the SM signature
  exact GaugeTheorySpace.gauge_signature_rigidity S h_rcc T h_admissible

end Terminality
end NemS
