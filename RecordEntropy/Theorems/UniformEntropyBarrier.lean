import RecordEntropy.Core.EntropyFinite
import ArrowOfTime.Core.RecordFiltration
import ArrowOfTime.Examples.Toy
import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders
import SelectorStrength.Core.AntiDecider
import SelectorStrength.Theorems.BarrierSchema

set_option autoImplicit false

/-!
# RecordEntropy.Theorems.UniformEntropyBarrier

**Paper 42: Uniform entropy decision barrier.**

Codes encode (filtration, time t, number n). EntropyOfCode(c) returns the record
entropy of the encoded filtration at the encoded time. The predicate
T(c) := (EntropyOfCode(c) = n(c)) is extensional and nontrivial on codes.
Under AntiDeciderClosed and hFP, no total-effective decider exists for T over
encoded instances.
-/

namespace RecordEntropy

open ArrowOfTime
open ArrowOfTime.RecordFiltration
open ArrowOfTime.Toy

/-- Index for encodable filtrations; extensible. -/
inductive FiltIndex
  | toy
  deriving DecidableEq

/-- Code encoding (filtration index, time t, claimed value n). -/
structure EntropyCode where
  filt : FiltIndex
  t : Nat
  n : Nat
  deriving DecidableEq

/-- Record entropy of the encoded filtration at the encoded time.
For Toy: t=0 has 2 world-types, t≥1 has 4. -/
def entropyOfCode : EntropyCode → Nat
  | ⟨FiltIndex.toy, 0, _⟩ => 2
  | ⟨FiltIndex.toy, _, _⟩ => 4

/-- **Uniform entropy-claim predicate:** T(c) := (EntropyOfCode(c) = n(c)). -/
def uniformEntropyClaim (c : EntropyCode) : Prop :=
  entropyOfCode c = c.n

/-- The uniform entropy claim is extensional for equality on codes. -/
theorem uniformEntropyClaim_extensional :
    SelectorStrength.Extensional (· = ·) uniformEntropyClaim := by
  intro x y heq
  rw [heq]

/-- The uniform entropy claim is nontrivial: (toy, 0, 2) holds, (toy, 0, 3) does not. -/
theorem uniformEntropyClaim_nontrivial :
    SelectorStrength.Nontrivial uniformEntropyClaim := by
  refine ⟨⟨⟨FiltIndex.toy, 0, 2⟩, rfl⟩, ⟨⟨FiltIndex.toy, 0, 3⟩, by simp only [uniformEntropyClaim, entropyOfCode]; norm_num⟩⟩

/-- **Uniform entropy decision barrier:** Under AntiDeciderClosed and hFP at strength S,
no total decider in Sbool exists for the uniform entropy-claim predicate on codes. -/
theorem no_total_decider_uniform_entropy
    (Sbool : SelectorStrength.Strength EntropyCode Bool)
    (Sα : SelectorStrength.Strength EntropyCode EntropyCode)
    (hAnti : SelectorStrength.AntiDeciderClosed Sbool Sα)
    (hFP : ∀ F : EntropyCode → EntropyCode, Sα F → ∃ d : EntropyCode, d = F d) :
    ¬ SelectorStrength.DecidableAt Sbool uniformEntropyClaim :=
  SelectorStrength.no_total_decider_at_strength_nontrivial (· = ·) uniformEntropyClaim
    uniformEntropyClaim_extensional uniformEntropyClaim_nontrivial Sbool Sα hAnti hFP

end RecordEntropy
