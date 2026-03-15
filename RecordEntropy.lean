import RecordEntropy.Core.EntropyFinite
import RecordEntropy.Core.HiddenHistoryEntropy
import RecordEntropy.Theorems.Monotonicity
import RecordEntropy.Theorems.NoncomputabilityBarrier
import RecordEntropy.Theorems.UniformEntropyBarrier
import RecordEntropy.Examples.ToyEntropy

/-!
# RecordEntropy — Paper 42

Root barrel for Record Entropy and Noncomputability.

Record entropy H(t) as cardinality of stage world-types; monotonicity and
strict monotonicity under refinement; fiber-based hidden-history entropy
(Core.HiddenHistoryEntropy); uniform entropy decision barrier
(Theorems.UniformEntropyBarrier); toy witness (Examples.ToyEntropy).
-/
