import NemS.Core.Basics

/-!
# NemS.Visibility.Recordability

A framework satisfies *evaluation-recordability* with respect to a type `E`
of evaluator/semantic choices if there is an injective map from `E` into
the record statements of the framework.

This formalizes: "which evaluator was applied is itself a recordable fact."
The injectivity ensures distinct evaluator choices produce distinct record
statements, so they cannot be collapsed without loss of observational content.
-/


namespace NemS

namespace Framework

variable (F : Framework)

/-- `Recordable F E` witnesses that evaluator choices of type `E` can be
injectively tagged as record statements in `F`.

This is the abstract form of "evaluation-recordability": the use of any
evaluator/semantic rule leaves a stable, distinguishable record trace. -/
structure Recordable (E : Type) where
  /-- Embed an evaluator choice as a record statement. -/
  tag        : E → F.Rec
  /-- Different evaluator choices produce different record statements. -/
  injective  : Function.Injective tag

namespace Recordable

variable {F : Framework} {E : Type}

/-- Two distinct evaluator choices produce distinct record tags. -/
theorem tag_ne {rec : F.Recordable E} {e₁ e₂ : E} (h : e₁ ≠ e₂) :
    rec.tag e₁ ≠ rec.tag e₂ :=
  fun heq => h (rec.injective heq)

end Recordable

end Framework

end NemS
