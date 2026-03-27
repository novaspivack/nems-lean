import NemS.Physical.UniversalComputation
import NemS.Diagonal.ASR
import NemS.MFRR.DiagonalBarrier

/-!
# NemS.Physical.ASRFromUCT

The key theorem: Physical Universal Computation (PhysUCT) implies
Diagonal Capability (ASR).

This is the "physical incompleteness" upgrade: the diagonal barrier
is not contingent on an exotic ASR assumption, but follows from the
mundane fact that the universe can host universal computation and
express halting as a record-level fact.

## Main result

`physUCT_implies_diagonalCapable`: if a framework has PhysUCT,
then it is diagonal-capable (carries an ASR structure).

The construction is straightforward: PhysUCT already provides the
encoding and halting-expressibility; we just need to package it
as an ASR structure by defining the RT predicate appropriately.
-/

namespace NemS
namespace Physical

open NemS.Diagonal
open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

/-- **Physical Incompleteness Theorem (construction lemma).**

If a framework has Physical Universal Computation capability (PhysUCT),
then it is diagonal-capable: it carries an ASR structure.

The construction is immediate: PhysUCT provides exactly the data
needed for ASR (RT, encode, encode_computable, halts_iff_RT). -/
def physUCT_implies_ASR
    {F : Framework} (uct : PhysUCT F) :
    ASR F :=
  ⟨uct.RT, uct.encode, uct.encode_computable, uct.halts_iff_RT⟩

/-- **Physical Incompleteness Theorem.**

If a framework has PhysUCT, then it is diagonal-capable,
and therefore the diagonal barrier applies: record-truth on the
ASR fragment is not computably decidable.

This is the "headline" form: physical universal computation implies
incompleteness (no total algorithmic ToE on diagonal-capable records). -/
@[reducible]
def physUCT_implies_diagonalCapable
    {F : Framework} (uct : PhysUCT F) :
    NemS.MFRR.DiagonalCapable F :=
  ⟨physUCT_implies_ASR uct⟩

/-- **Corollary: PhysUCT implies RT not computable.**

If a framework has PhysUCT, then its record-truth predicate is
not computably decidable. -/
theorem physUCT_implies_RT_not_computable
    {F : Framework} (uct : PhysUCT F) :
    ¬ ComputablePred uct.RT :=
  NemS.Diagonal.no_total_effective_rt_decider (physUCT_implies_ASR uct)

/-- **Theorem alias: Physical Incompleteness.**

Same as `physUCT_implies_RT_not_computable`. Citation-friendly name for the
synthesis paper (Paper 78): closed-universe no-total-effective-decider. -/
theorem physical_incompleteness
    {F : Framework} (uct : PhysUCT F) :
    ¬ ComputablePred uct.RT :=
  physUCT_implies_RT_not_computable uct

/-- **Theorem alias: No Total Algorithmic ToE.**

Same as `physUCT_implies_RT_not_computable`. Citation-friendly name for the
synthesis paper: no total algorithmic theory of everything on diagonal-capable records. -/
theorem no_total_algorithmic_toe
    {F : Framework} (uct : PhysUCT F) :
    ¬ ComputablePred uct.RT :=
  physUCT_implies_RT_not_computable uct

end Physical
end NemS
