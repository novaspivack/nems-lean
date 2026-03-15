import NemS.Prelude

/-!
# InternalitySchema.Core.SystemTask

Defines the abstract interface for Program I: Internality / Outsourcing Schema.
-/

namespace InternalitySchema

universe u v w

/-- A `SystemTaskInterface` defines the abstract setting for internality reasoning.
- `System` : the type of systems (e.g. Frameworks, TheorySpaces).
- `Task`   : the type of tasks or predicates (e.g. Selectors, Deciders).
- `Structure` : the type of added structure (e.g. external bits, oracles).
-/
structure SystemTaskInterface where
  System : Type u
  Task : Type v
  Structure : Type w
  LoadBearing : System → Task → Prop
  InternallyRealizable : System → Task → Prop
  CompletedBy : System → Task → Structure → Prop
  InternalTo : Structure → System → Prop
  /-- Bridge: if a task is completed by an internal structure, it is internally realizable. -/
  realizable_of_completed_internal : ∀ {s : System} {t : Task} {x : Structure},
    CompletedBy s t x → InternalTo x s → InternallyRealizable s t

namespace SystemTaskInterface

variable {I : SystemTaskInterface}

/-- A system outsources a task if it is completed by a non-internal structure. -/
def Outsources (s : I.System) (t : I.Task) : Prop :=
  ∃ x : I.Structure, I.CompletedBy s t x ∧ ¬ I.InternalTo x s

end SystemTaskInterface

end InternalitySchema
