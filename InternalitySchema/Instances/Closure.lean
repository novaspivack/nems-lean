import InternalitySchema.Core.SystemTask
import NemS.Core.Trichotomy

/-!
# InternalitySchema.Instances.Closure

Instantiates the InternalitySchema for the NEMS framework.
-/

namespace InternalitySchema

open NemS

/-- 
Instantiate `SystemTaskInterface` for NEMS.
- `System` : `Framework`
- `Task`   : `F.Selector` (represented as a dependent type)
- `Structure` : `F.Selector` (the actual selector added)
-/
def NEMSInterface : SystemTaskInterface where
  System := Framework
  Task := (F : Framework) → F.Selector
  Structure := (F : Framework) → F.Selector
  LoadBearing F _ := ¬ F.ObsCategorical
  InternallyRealizable F _ := ∃ S : F.Selector, True -- Simplified
  CompletedBy F T S := ∀ M, (T F).sel M = (S F).sel M
  InternalTo _ _ := True -- This is where the IsInternal predicate would go
  realizable_of_completed_internal := fun {s} {t} {x} _ _ => ⟨x s, True.intro⟩

-- Note: The above is a bit clunky due to the dependent types. 
-- A better way is to fix the Framework F.

def NEMSInterfaceFixed (F : Framework) (IsInternal : F.Selector → Prop) : SystemTaskInterface where
  System := Unit
  Task := F.Selector
  Structure := F.Selector
  LoadBearing _ _ := ¬ F.ObsCategorical
  InternallyRealizable _ _ := ∃ S : F.Selector, IsInternal S
  CompletedBy _ T S := T = S
  InternalTo S _ := IsInternal S
  realizable_of_completed_internal := fun {s} {t} {x} _ hInt => ⟨x, hInt⟩

end InternalitySchema
