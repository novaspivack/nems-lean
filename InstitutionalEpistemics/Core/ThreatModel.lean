-- Instance space and threat model (Paper 40)
import InstitutionalEpistemics.Core.Roles

variable (Instance : Type*) [Fintype Instance]

/-- Truth labeling of instances. -/
def Truth := Instance → Bool

/-- Adversary: produces a set of instances (the "attack" set). -/
def Adversary := Finset Instance

/-- Failure set: instances where the protocol fails (e.g., wrong or abstain when should decide). -/
def FailSet := Finset Instance

/-- Certified coverage: instances that receive a correct verdict. -/
def CertifiedCover (Instance : Type*) := Finset Instance
