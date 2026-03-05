-- Roles and diversity (Paper 40)
import Mathlib.Data.Fintype.Card

variable (n : ℕ) (Instance : Type*)

/-- A role is an index type (finite in practice). -/
structure Role (n : ℕ) where
  idx : Fin n
  deriving DecidableEq

instance (n : ℕ) : Fintype (Role n) := Fintype.ofEquiv (Fin n)
  { toFun := Role.mk
    invFun := Role.idx
    left_inv := fun _ => rfl
    right_inv := fun ⟨_, _⟩ => rfl }

/-- Coverage set: which instances a role can certify. -/
def Cover (Instance : Type*) := Instance → Prop

/-- Two roles are equivalent for coverage if they have the same coverage set. -/
def RoleEquiv (n : ℕ) (Instance : Type*) (cov : Role n → Cover Instance) (r₁ r₂ : Role n) : Prop :=
  ∀ i, cov r₁ i ↔ cov r₂ i

/-- Diversity: at least two roles with distinct coverage sets. -/
def Diversity (Instance : Type*) (n : ℕ) (cov : Role n → Cover Instance) : Prop :=
  ∃ r₁ r₂ : Role n, r₁ ≠ r₂ ∧ ¬(RoleEquiv n Instance cov r₁ r₂)
