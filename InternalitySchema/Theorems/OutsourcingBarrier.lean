import InternalitySchema.Core.SystemTask

/-!
# InternalitySchema.Theorems.OutsourcingBarrier

The main theorem schema for the Internality / Outsourcing program.
-/

namespace InternalitySchema

open SystemTaskInterface

variable {I : SystemTaskInterface}

/-- 
**Generic Outsourcing Barrier** (Program I, Theorem 1)

If a task is load-bearing for a system and is not internally realizable,
then any successful completion of that task necessarily outsources
to non-internal structure.
-/
theorem outsourcing_barrier 
    (s : I.System) (t : I.Task) (x : I.Structure)
    (_hLoad : I.LoadBearing s t)
    (hNotInternal : ¬ I.InternallyRealizable s t)
    (hComplete : I.CompletedBy s t x) :
    ¬ I.InternalTo x s := by
  intro hInternal
  have hRealizable := I.realizable_of_completed_internal hComplete hInternal
  contradiction

/--
**Outsourcing Witness Theorem**

Under the same conditions, the system outsources the task.
-/
theorem outsources_witness
    (s : I.System) (t : I.Task) (x : I.Structure)
    (hLoad : I.LoadBearing s t)
    (hNotInternal : ¬ I.InternallyRealizable s t)
    (hComplete : I.CompletedBy s t x) :
    I.Outsources s t := by
  exists x
  constructor
  · exact hComplete
  · exact outsourcing_barrier s t x hLoad hNotInternal hComplete

end InternalitySchema
