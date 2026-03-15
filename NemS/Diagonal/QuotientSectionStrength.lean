import NemS.Diagonal.Instantiation
import NemS.Diagonal.QuotientSectionBridge
import SelfReference.Instances.NEMS

open SelfReference.Instances.NEMS

/-!
# NemS.Diagonal.QuotientSectionStrength

**SPEC_69_DSL — Flagship concrete instance: no computable decider on the halting framework.**

This module proves that on the halting framework, no computable total decider exists
for any nontrivial extensional predicate. This is the "fully instantiated computable
example" called for in Paper 29's future directions (i).

The result composes:
- `nems_rt_no_computable_bool_decider` (SelfReference.Instances.NEMS) — uses
  `Nat.Partrec.Code.fixed_point` to discharge the hFP premise
- The halting framework's structure (Model = ℕ, ObsEq = same halting set)
- A concrete nontrivial extensional predicate: halts on input 0
-/

namespace NemS
namespace Diagonal

open Encodable Denumerable
open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

/-- **Halts-on-zero predicate**: model index `n` satisfies T iff the program
coded by `n` halts on input 0. Extensional for ObsEq (same halting set). -/
def haltsOnZero (n : ℕ) : Prop :=
  (eval (ofNat Code n) 0).Dom

/-- `haltsOnZero` is extensional: if two codes have the same evaluation,
they agree on halting at 0. -/
theorem haltsOnZero_extensional
    {e₁ e₂ : Code} (heval : eval e₁ = eval e₂) :
    haltsOnZero (Encodable.encode e₁) ↔ haltsOnZero (Encodable.encode e₂) := by
  simp only [haltsOnZero]
  rw [show ofNat Code (Encodable.encode e₁) = e₁ from Denumerable.ofNat_encode e₁,
      show ofNat Code (Encodable.encode e₂) = e₂ from Denumerable.ofNat_encode e₂,
      heval]

/-- `haltsOnZero` has a true instance: Code.zero halts on 0. -/
theorem haltsOnZero_true : ∃ c : Code, haltsOnZero (Encodable.encode c) := by
  use Code.zero
  simp only [haltsOnZero, Denumerable.ofNat_encode]
  show (eval Code.zero 0).Dom
  have heval : eval Code.zero 0 = Part.some 0 := rfl
  rw [heval]
  trivial

/-- `haltsOnZero` has a false instance: the code for χ₁ halts only on 1, not 0. -/
theorem haltsOnZero_false : ∃ c : Code, ¬ haltsOnZero (Encodable.encode c) := by
  let c := Classical.choose (Code.exists_code.1 (partrec_singleton_halting 1))
  use c
  simp only [haltsOnZero, Denumerable.ofNat_encode]
  have heval : eval c = fun x => if x = 1 then Part.some 0 else Part.none :=
    Classical.choose_spec (Code.exists_code.1 (partrec_singleton_halting 1))
  rw [heval]
  simp

/-- **Flagship: halting framework — no computable decider for halts-on-zero.**

On the halting framework, no computable total Boolean decider exists for the
nontrivial extensional predicate "halts on input 0". This is the concrete
instance of the selector-strength barrier at the computable level.

Proof: Apply `nems_rt_no_computable_bool_decider` to `haltsOnZero` with
extensionality and nontriviality witnesses. -/
theorem halting_framework_no_decider_at_computable :
    ¬ ∃ δ : ℕ → Bool,
        Computable δ ∧ ∀ n, δ n = true ↔ haltsOnZero n :=
  nems_rt_no_computable_bool_decider haltsOnZero
    haltsOnZero_extensional haltsOnZero_true haltsOnZero_false

/-- **Corollary**: No computable decider exists for any nontrivial extensional
predicate on the halting framework.

This re-exports the theorem with a more general statement for downstream use.
The barrier schema applies to any T that is extensional (for eval-equality)
and nontrivial. -/
theorem halting_framework_no_total_computable_decider
    (T : ℕ → Prop)
    (hExt : ∀ {e₁ e₂ : Code}, eval e₁ = eval e₂ →
      (T (Encodable.encode e₁) ↔ T (Encodable.encode e₂)))
    (hTrue : ∃ c : Code, T (Encodable.encode c))
    (hFalse : ∃ c : Code, ¬ T (Encodable.encode c)) :
    ¬ ∃ δ : ℕ → Bool, Computable δ ∧ ∀ n, δ n = true ↔ T n :=
  nems_rt_no_computable_bool_decider T hExt hTrue hFalse

end Diagonal
end NemS
