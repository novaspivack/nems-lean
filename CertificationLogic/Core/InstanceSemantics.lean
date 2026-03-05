import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# CertificationLogic.Core.InstanceSemantics — Paper 50 Capstone

Finite instance semantics: Instance, Truth, Verdict, Verifier, SoundOnCover, Coverage.
-/

set_option autoImplicit false

namespace CertificationLogic

/-- Three-valued verdict for certification. -/
inductive Verdict | accept | reject | abstain
  deriving DecidableEq

/-- Verifier: maps instances to verdicts. -/
def Verifier (α : Type _) : Type _ := α → Verdict

/-- Ground truth labeling (for soundness-on-coverage). -/
def Truth (α : Type _) : Type _ := α → Bool

/-- **SoundOnCover**: On cover C, verifier matches truth; outside C, abstains. -/
def SoundOnCover {α : Type*} (truth : Truth α) (V : Verifier α) (C : Finset α) : Prop :=
  (∀ x ∈ C, (V x = Verdict.accept ↔ truth x = true) ∧
            (V x = Verdict.reject ↔ truth x = false)) ∧
  (∀ x, x ∉ C → V x = Verdict.abstain)

/-- **Coverage**: instances where verifier does not abstain. -/
def coverage {α : Type*} [Fintype α] [DecidableEq α] (V : Verifier α) : Finset α :=
  Finset.univ.filter (fun x => V x ≠ Verdict.abstain)

@[simp]
theorem mem_coverage {α : Type*} [Fintype α] [DecidableEq α] (V : Verifier α) (x : α) :
    x ∈ coverage V ↔ V x ≠ Verdict.abstain := by
  simp [coverage]

/-- Canonical verifier for a set C: accept on C, abstain elsewhere. -/
def canonicalVerifier {α : Type*} [DecidableEq α] (C : Finset α) : Verifier α :=
  fun x => if x ∈ C then Verdict.accept else Verdict.abstain

@[simp]
theorem coverage_canonicalVerifier {α : Type*} [Fintype α] [DecidableEq α] (C : Finset α) :
    coverage (canonicalVerifier C) = C := by
  ext x; simp [coverage, canonicalVerifier]

end CertificationLogic
