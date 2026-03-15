import NemS.Diagonal.ASR
import NemS.Diagonal.Barrier

/-!
# Hypercomputation.Examples.RecordTruth

**Record-truth predicate example (Paper 35).**

Wraps the NEMS diagonal barrier (ASR ⇒ RT not computable) in the
Hypercomputation interface. No internal total effective hypercomputer
exists for record-truth on any diagonal-capable framework.
-/

set_option autoImplicit false

namespace Hypercomputation
namespace Examples

/-- **No internal hypercomputer for record-truth (Paper 35).**

Given any framework with an ASR (Arithmetic Self-Reference) structure,
record-truth (RT) is not computably decidable. Any purported total effective
hypercomputer for RT would contradict the diagonal barrier.

This is the semantic/record-truth case from Paper 35, formalized. -/
theorem no_internal_hypercomputer_for_record_truth
    {F : NemS.Framework} (asr : NemS.Diagonal.ASR F) :
    ¬ ComputablePred asr.RT :=
  NemS.Diagonal.no_total_effective_rt_decider asr

/-- **No total effective record-truth hypercomputer.** Alias. -/
theorem no_total_effective_record_truth_hypercomputer
    {F : NemS.Framework} (asr : NemS.Diagonal.ASR F) :
    ¬ ComputablePred asr.RT :=
  no_internal_hypercomputer_for_record_truth asr

end Examples
end Hypercomputation
