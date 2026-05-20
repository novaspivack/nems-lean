import CertificationLogic.Core.Protocols
import Mathlib.Data.Finset.Basic

/-!
# CertificationLogic.Core.Formulas — Paper 50 Capstone

Formulas as claim sets (Finset Instance). Derivable rules mirroring protocol combinators.
-/

set_option autoImplicit false

namespace CertificationLogic

variable {Instance : Type*} [Fintype Instance] [DecidableEq Instance]
variable {n : ℕ} [DecidableEq (Role n)]

/-- A claim set: instances certified (formula = Finset Instance). -/
abbrev Formula := Finset Instance

/-- Coverage map: each role covers a set of instances. -/
abbrev CovMap := Role n → Finset Instance

/-- **Derivable** (⊢_S C): syntactic proof system mirroring protocol combinators.
  Stratum S is abstract; for single-stratum use Unit. -/
inductive Derivable {Stratum : Type*} (cov : Role n → Finset Instance)
    (ax : Stratum → Finset Instance → Prop) : Stratum → Finset Instance → Prop
  | ax (S : Stratum) (C : Finset Instance) (h : ax S C) : Derivable cov ax S C
  | union (S : Stratum) (C₁ C₂ : Finset Instance) (h1 : Derivable cov ax S C₁)
      (h2 : Derivable cov ax S C₂) : Derivable cov ax S (C₁ ∪ C₂)
  | subset (S : Stratum) (C C' : Finset Instance) (h : Derivable cov ax S C)
      (hsub : C' ⊆ C) : Derivable cov ax S C'
  | stratumMono (S S' : Stratum) (C : Finset Instance) (_h : Derivable cov ax S C)
      (hle : S = S') : Derivable cov ax S' C  -- intended: S ≤ S' (strength preorder, Paper 29)

/-- Axiom family induced by coverage: C is an axiom at S iff C ⊆ cov r for some role r. -/
def axFromCov {Stratum : Type*} (cov : Role n → Finset Instance) (_S : Stratum)
    (C : Finset Instance) : Prop :=
  ∃ r : Role n, C ⊆ cov r

end CertificationLogic
