import CertificationLogic.Core.Protocols
import Mathlib.Data.Finset.Basic

/-!
# CertificationLogic.Core.Formulas — Paper 50 Capstone

Formulas as claim sets (Finset Instance). Derivable rules mirroring protocol combinators.
-/

set_option autoImplicit false

variable (Instance : Type*) [Fintype Instance] [DecidableEq Instance]
variable (n : ℕ) [DecidableEq (InstitutionalEpistemics.Role n)]

namespace CertificationLogic

/-- A claim set: instances certified (formula = Finset Instance). -/
def Formula (_Instance : Type*) : Type := Finset Instance

/-- Coverage map: each role covers a set of instances. -/
def CovMap : Type := InstitutionalEpistemics.Role n → Finset Instance

variable {Instance n}

/-- **Derivable** (⊢_S C): syntactic proof system mirroring protocol constructors.
  Stratum S is abstract; for single-stratum use Unit. -/
inductive Derivable {Stratum : Type*} (cov : CovMap) (ax : Stratum → Formula Instance → Prop) :
    Stratum → Formula Instance → Prop
  | ax (S : Stratum) (C : Formula Instance) (h : ax S C) : Derivable cov ax S C
  | union (S : Stratum) (C₁ C₂ : Formula Instance) (h1 : Derivable cov ax S C₁)
      (h2 : Derivable cov ax S C₂) : Derivable cov ax S (C₁ ∪ C₂)
  | subset (S : Stratum) (C C' : Formula Instance) (h : Derivable cov ax S C)
      (hsub : C' ⊆ C) : Derivable cov ax S C'
  | stratumMono (S S' : Stratum) (C : Formula Instance) (_h : Derivable cov ax S C)
      (hle : S = S') : Derivable cov ax S' C  -- intended: S ≤ S' (strength preorder, Paper 29)

/-- Axiom family induced by coverage: C is an axiom at S iff C ⊆ cov r for some role r. -/
def axFromCov {Stratum : Type*} (cov : CovMap) (_S : Stratum) (C : Formula Instance) : Prop :=
  ∃ r, C ⊆ cov r

end CertificationLogic
