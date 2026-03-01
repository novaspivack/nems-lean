import NemS.Quantum.MatrixBasics

/-!
# NemS.Quantum.Effects

Quantum effects: operators E with 0 ≤ E ≤ I (in the Loewner order).

An effect is a Hermitian operator E satisfying:
- E is positive semidefinite (0 ≤ E)
- I - E is positive semidefinite (E ≤ I)
-/

namespace NemS
namespace Quantum

/-- A quantum effect on n-dimensional Hilbert space:
a Hermitian operator E with IsPosSemidef E and IsPosSemidef (I - E). -/
structure Effect (n : ℕ) where
  /-- The underlying operator. -/
  op : Op n
  /-- The operator is Hermitian. -/
  hermitian : op.IsHermitian
  /-- The operator is positive semidefinite (0 ≤ E). -/
  psd : IsPosSemidef op
  /-- The operator is bounded by identity (E ≤ I). -/
  bounded : IsPosSemidef (1 - op)

namespace Effect

variable {n : ℕ}

/-- The zero effect. -/
def zero : Effect n where
  op := 0
  hermitian := Matrix.isHermitian_zero
  psd := isPosSemidef_zero
  bounded := by simp; exact isPosSemidef_one

/-- The identity effect. -/
def one : Effect n where
  op := 1
  hermitian := Matrix.isHermitian_one
  psd := isPosSemidef_one
  bounded := by simp; exact isPosSemidef_zero

/-- Two effects can be added if their sum has op ≤ I. -/
def add (E F : Effect n) (h : IsPosSemidef (1 - (E.op + F.op))) : Effect n where
  op := E.op + F.op
  hermitian := E.hermitian.add F.hermitian
  psd := isPosSemidef_add E.psd F.psd
  bounded := h

end Effect

end Quantum
end NemS
