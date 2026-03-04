import NemS.Prelude

/-!
# EpistemicAgency.Core.ClaimDomain

**Finite claim domain, verdicts, verifiers, and soundness-on-coverage (Paper 31).**

A finite claim domain bundles claim identifiers with a ground-truth labeling.
Verifiers output accept / reject / abstain. Soundness-on-coverage ties verifier
behavior to a designated coverage set and truth.
-/

set_option autoImplicit false

namespace EpistemicAgency

/-- Three-valued verdict for a claim. -/
inductive Verdict
  | accept
  | reject
  | abstain
  deriving DecidableEq

/-- A **claim domain** is a finite type of claim IDs and a ground-truth labeling. -/
structure ClaimDomain where
  ClaimId : Type
  Truth : ClaimId → Bool
  fintype : Fintype ClaimId
  decidableEq : DecidableEq ClaimId

namespace ClaimDomain

variable (D : ClaimDomain)

instance : Fintype D.ClaimId := D.fintype
instance : DecidableEq D.ClaimId := D.decidableEq

/-- **Verifier**: function from claim IDs to verdicts. -/
def Verifier := D.ClaimId → Verdict

instance : DecidableEq (Verifier D) :=
  inferInstanceAs (DecidableEq (D.ClaimId → Verdict))

/-- **Soundness-on-coverage**: on cover `C`, verifier agrees with truth;
  outside `C`, verifier abstains. -/
def SoundOnCover (V : Verifier D) (C : Finset D.ClaimId) : Prop :=
  (∀ c ∈ C, (V c = Verdict.accept ↔ D.Truth c = true) ∧ (V c = Verdict.reject ↔ D.Truth c = false)) ∧
  (∀ c, c ∉ C → V c = Verdict.abstain)

/-- **Cover** for a verifier: we use `Finset ClaimId`; the existence of such a set
  with SoundOnCover is the contract (each verifier has some cover when sound). -/
def Cover (_V : Verifier D) := Finset D.ClaimId

end ClaimDomain

end EpistemicAgency
