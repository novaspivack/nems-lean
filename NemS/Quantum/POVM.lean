import NemS.Quantum.Effects

/-!
# NemS.Quantum.POVM

Positive Operator-Valued Measures (POVMs): finite families of effects
that sum to the identity.
-/

namespace NemS
namespace Quantum

open BigOperators

/-- A POVM of size k on n-dimensional Hilbert space:
a finite family of k effects whose operator-sum equals I. -/
structure POVM (n k : ℕ) where
  /-- The k effects. -/
  effects : Fin k → Effect n
  /-- They sum to identity. -/
  sum_eq_one : (∑ i, (effects i).op) = 1

namespace POVM

variable {n k : ℕ}

/-- Extract the i-th effect operator from a POVM. -/
def getOp (P : POVM n k) (i : Fin k) : Op n :=
  (P.effects i).op

/-- The sum of POVM operators is identity. -/
theorem sum_ops_eq_one (P : POVM n k) :
    (∑ i, P.getOp i) = 1 :=
  P.sum_eq_one

end POVM

end Quantum
end NemS
