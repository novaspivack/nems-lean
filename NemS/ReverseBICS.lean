import NemS.ReverseBICS.BICS
import NemS.ReverseBICS.BICS_Implies_NEMS
import NemS.ReverseBICS.BICS_To_PSC

/-!
# NemS.ReverseBICS

Reverse direction: Born Internal & Complete Semantics (BICS) ⇒ NEMS ⇒ PSC.

This module family proves that if quantum probability (Born rule) provides the internal,
complete semantics for records (BICS), then external model selection is impossible (NEMS),
and under existing closure reductions (ER + semantic visibility), the theory must satisfy
PSC bundle / Full PSC.

This completes the fixed-point architecture:
- Forward (Papers 8, 13): PSC ⇒ Born semantics (uniqueness proved, existence cited)
- Reverse (Paper 14): BICS ⇒ NEMS ⇒ PSC

Main theorems:
- `bics_implies_nems`: BICS F → NEMS F
- `bics_and_er_imply_pscBundle`: BICS F → ER F → PSCBundle F
- `bics_and_er_and_semvis_imply_fullPSC`: BICS F → ER F → SemanticVisibility F → FullPSC F
-/
