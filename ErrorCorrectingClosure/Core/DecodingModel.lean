/-!
# ErrorCorrectingClosure.Core.DecodingModel

**Paper 43: Decoding model — records as codeword-like constraints.**

Record fragments are encoded as **codes** (instance + claimed outcome). A **decoder claim**
is the predicate that the encoded instance's consistency matches the claimed value.
Consistency is interpreted semantically (e.g. non-categoricity / selector necessity from
Closure); here we use a minimal type of instances and a consistency predicate for the
barrier instantiation.
-/

set_option autoImplicit false

namespace ErrorCorrectingClosure

/-- **Instance index**: encodes which "record fragment" or scenario we are decoding.
Extensible (e.g. from a filtration or protocol). -/
inductive InstanceIndex
  | consistent  -- instance that decodes to consistent
  | inconsistent
  deriving DecidableEq

/-- **Decode code**: encodes (instance, claimed outcome). A total decoder would
decide whether the instance is consistent; the claim is what the code asserts. -/
structure DecodeCode where
  instanceIdx : InstanceIndex
  claimed : Bool  -- true = "claim consistent", false = "claim inconsistent"
  deriving DecidableEq

/-- Whether the given instance is semantically "consistent" (decodable).
In the barrier we need at least one consistent and one inconsistent instance. -/
def isConsistent : InstanceIndex → Bool
  | InstanceIndex.consistent => true
  | InstanceIndex.inconsistent => false

/-- **Uniform decoder-claim predicate**: T(c) := (isConsistent(c.instance) = c.claimed).
A total-effective decider for this predicate would be a "universal decoder" that
decides consistency for arbitrary encoded instances. -/
def decoderClaim (c : DecodeCode) : Prop :=
  isConsistent c.instanceIdx = c.claimed

end ErrorCorrectingClosure
