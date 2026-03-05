/-!
# LawCalibration.Core.LawUpdate

**Paper 44: Law object and update operator.**

A **law** type and an update operator U : Law → Law driven by closure constraints.
Fixed points are equilibria; minimality is kept abstract at the predicate level (no MDL).
We use a minimal concrete type (two elements) so the barrier can be instantiated without axioms.
-/

set_option autoImplicit false

namespace LawCalibration

/-- **Law**: minimal type with two elements for fixed-point multiplicity and selection barrier.
Extensible to larger types in applications. -/
inductive Law
  | minimal  -- designated "minimal" fixed point
  | other    -- another fixed point (multiplicity)
  deriving DecidableEq

/-- **Law update operator**: U : Law → Law. Here id for simplicity; both elements are fixed points. -/
def lawUpdate : Law → Law := id

/-- **Fixed point**: ℓ is a fixed point when U(ℓ) = ℓ. -/
def IsFixedPoint (ℓ : Law) : Prop :=
  lawUpdate ℓ = ℓ

/-- **Minimal fixed point**: the designated minimal element (abstract predicate; no MDL). -/
def IsMinimalFixedPoint (ℓ : Law) : Prop :=
  ℓ = Law.minimal

/-- **Law code** (single-instance / toy): encodes (law candidate, claimed "is minimal").
Used only to illustrate multiplicity; the barrier is on the uniform predicate below. -/
structure LawCode where
  law : Law
  claimed : Bool  -- true = "claim minimal", false = "claim not minimal"
  deriving DecidableEq

/-- **Law-selector claim** (toy, single instance): T(c) := (IsMinimalFixedPoint c.law ↔ c.claimed = true).
Trivially decidable in the toy; the barrier is not claimed for this predicate. -/
def lawSelectorClaim (c : LawCode) : Prop :=
  (IsMinimalFixedPoint c.law ↔ c.claimed = true)

/-- **Instance index**: identifies a law-update instance (family of U, Min).
At least two instances for nontriviality of the uniform predicate. -/
inductive InstanceIndex
  | inst0  -- instance where minimal is the minimal fixed point
  | inst1  -- instance where other is the minimal fixed point
  deriving DecidableEq

/-- **Selector code** (uniform barrier): encodes (instance, candidate law, claimed).
The barrier applies to the predicate "candidate is a minimal fixed point for this instance" ↔ claimed. -/
structure LawInstanceCode where
  instanceId : InstanceIndex
  cand : Law
  claimed : Bool
  deriving DecidableEq

/-- **Minimality in instance**: for inst0, minimal is minimal; for inst1, other is minimal.
So the uniform predicate is nontrivial across the encoded family. -/
def isMinimalForInstance (i : InstanceIndex) (ℓ : Law) : Prop :=
  match i, ℓ with
  | InstanceIndex.inst0, Law.minimal => True
  | InstanceIndex.inst0, Law.other => False
  | InstanceIndex.inst1, Law.minimal => False
  | InstanceIndex.inst1, Law.other => True

/-- **Uniform law-selector claim**: T(c) := (isMinimalForInstance c.instanceId c.cand ↔ c.claimed = true).
No total-effective decider exists for this predicate under AntiDeciderClosed and hFP (barrier). -/
def uniformLawSelectorClaim (c : LawInstanceCode) : Prop :=
  (isMinimalForInstance c.instanceId c.cand ↔ c.claimed = true)

end LawCalibration
