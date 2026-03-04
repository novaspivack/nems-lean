-- Protocols and admissibility (Paper 40)
import InstitutionalEpistemics.Core.Roles
import InstitutionalEpistemics.Core.ThreatModel

variable (Instance : Type*) [Fintype Instance] (n : ℕ) [DecidableEq (Role n)]

namespace InstitutionalEpistemics

/-- A verifier verdict: accept, reject, or abstain. -/
inductive Verdict | accept | reject | abstain

/-- A protocol aggregates verdicts from roles. Admissible: no definitive verdict when all abstain. -/
structure Protocol (Role : Type*) (cov : Role → Instance → Prop) where
  aggregate : (Role → Verdict) → Verdict
  admissible : ∀ f, (∀ r, f r = Verdict.abstain) → aggregate f = Verdict.abstain

/-- Union protocol: accept if any accepts; reject if any rejects (and none accept); else abstain.
    Admissible by construction. -/
def unionAggregate (f : Role n → Verdict) : Verdict :=
  if ∃ r, f r = Verdict.accept then Verdict.accept
  else if ∃ r, f r = Verdict.reject then Verdict.reject
  else Verdict.abstain

theorem union_admissible (f : Role n → Verdict) (h : ∀ r, f r = Verdict.abstain) :
    unionAggregate f = Verdict.abstain := by
  simp [unionAggregate]; intro r; exact h r

end InstitutionalEpistemics
