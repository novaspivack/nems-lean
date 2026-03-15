import InternalitySchema.Theorems.OutsourcingBarrier
import InternalitySchema.Instances.Closure

/-!
# InternalitySchema.Theorems.NEMSRecovery

Recovers NEMS results from the general InternalitySchema.
-/

namespace InternalitySchema

open NemS
open SystemTaskInterface

/--
**NEMS Recovery**

If a framework is non-categorical and has no internal selector,
then any purported selector is non-internal (outsourced).
-/
theorem nems_recovery (F : Framework) (IsInternal : F.Selector → Prop) (S : F.Selector)
    (hNC : ¬ F.ObsCategorical)
    (hNoInternal : ¬ ∃ S : F.Selector, IsInternal S) :
    ¬ IsInternal S := by
  let I := NEMSInterfaceFixed F IsInternal
  have hLoad : I.LoadBearing () S := hNC
  have hNotInt : ¬ I.InternallyRealizable () S := hNoInternal
  have hComp : I.CompletedBy () S S := rfl
  exact @outsourcing_barrier I () S S hLoad hNotInt hComp

end InternalitySchema
