import SemanticSelfDescription.Core.Claims
import SemanticSelfDescription.Core.SelfTheory
import SemanticSelfDescription.Core.SelfScope

/-!
# SemanticSelfDescription.Core.SelfErasure

**Weak and strong self-erasure: the hierarchy from final self-theory to semantic closure.**

- **WeakSelfErasing**: FinalSelfTheory ∧ SelfScoped — ruled out by no_final_self_theory.
- **StrongSelfErasing** / **SemanticClosureByTheory**: The full collapse condition — the system's
  realized semantics is exhausted by its internal semantic image, including claims about
  the theory's own verdict behavior. This is the flagship notion.

## Key definitions

- `WeakSelfErasing T` := FinalSelfTheory T ∧ SelfScoped F T
- `SemanticClosureByTheory F T` : final + selfScoped + image_complete + self_image_closed
- `StrongSelfErasing T` := SemanticClosureByTheory F T
- `SemanticRemainder T` : some code where T's verdict fails to match realized truth
-/

set_option autoImplicit false

namespace SemanticSelfDescription

universe u v

variable {W : Type u} (F : SelfSemanticFrame W)

open Verdict

/--
**Weak self-erasing** (data): a final self-theory that is also self-scoped.
-/
structure WeakSelfErasingData (T : InternalSelfTheory F) where
  final  : FinalSelfTheory T
  scope  : SelfScoped F T

/--
**Weak self-erasing** (Prop): exists a weak self-erasing witness for T.

Useful as an intermediate notion; immediately ruled out by no_final_self_theory.
-/
def WeakSelfErasing (T : InternalSelfTheory F) : Prop :=
  Nonempty (WeakSelfErasingData F T)

/--
**Semantic closure by theory**: the full collapse condition.

The theory closes the world's self-semantic space into its own exact image,
including claims about its own semantic action. No irreducible remainder.
-/
structure SemanticClosureByTheory (T : InternalSelfTheory F) where
  final      : FinalSelfTheory T
  selfScoped : SelfScoped F T

  /-- The theory's image is exact: verdict matches realized truth. -/
  image_complete :
    ∀ code : F.Code,
      (T.verdict code = yes ↔ F.selfSemanticTruth code) ∧
      (T.verdict code = no  ↔ ¬ F.selfSemanticTruth code)

  /-- Claims about T's verdict behavior are encodable in the frame. -/
  self_image_closed :
    ∀ code : F.Code,
      ∃ codeYes codeNo : F.Code,
        F.decode codeYes = selfScoped.SaysYesClaim code ∧
        F.decode codeNo  = selfScoped.SaysNoClaim code

/--
**Strong self-erasing** (data): witness of semantic closure by theory.
-/
structure StrongSelfErasingData (T : InternalSelfTheory F) where
  closure : SemanticClosureByTheory F T

/--
**Strong self-erasing** (Prop): the theory exhausts the realized semantic totality
while remaining closed under self-application. The real collapse condition.
-/
def StrongSelfErasing (T : InternalSelfTheory F) : Prop :=
  Nonempty (StrongSelfErasingData F T)

/--
**Semantic remainder**: some code where T's verdict fails to match realized truth.

A positive formulation: the theory leaves irreducible remainder.
-/
def SemanticRemainder (T : InternalSelfTheory F) : Prop :=
  ∃ code : F.Code,
    ¬ ((T.verdict code = yes ↔ F.selfSemanticTruth code) ∧
       (T.verdict code = no  ↔ ¬ F.selfSemanticTruth code))

end SemanticSelfDescription
