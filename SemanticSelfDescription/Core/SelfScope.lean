import SemanticSelfDescription.Core.Claims
import SemanticSelfDescription.Core.SelfTheory

/-!
# SemanticSelfDescription.Core.SelfScope

**Self-scoped theories: the frame can encode claims about the theory's own verdicts.**

A theory `T` is **self-scoped** if the claim family includes claims about what `T` says
on each code — i.e. meta-claims about T's own semantic activity. This is the first
upgrade beyond mere final self-theory: the theory's verdict behavior lies inside
the same claim universe it purports to close.

## Key definitions

- `SelfScoped F T` : SaysYesClaim, SaysNoClaim with correctness
- `StronglySelfScoped F T` : extends with WrongClaim
-/

set_option autoImplicit false

namespace SemanticSelfDescription

universe u v

variable {W : Type u} (F : SelfSemanticFrame W) (T : InternalSelfTheory F)

open Verdict

/--
**Self-scoped**: the frame can internally encode claims about T's verdict behavior.

- `SaysYesClaim code` : the claim "T says yes on code"
- `SaysNoClaim code` : the claim "T says no on code"
- Correctness: realized truth of these claims matches T's actual verdicts

This expresses that the theory's own semantic activity lies within the
claim family it purports to describe.
-/
structure SelfScoped where
  SaysYesClaim : F.Code → F.Claim
  SaysNoClaim  : F.Code → F.Claim

  saysYes_correct :
    ∀ code : F.Code, F.RealizedTrue (SaysYesClaim code) ↔ T.verdict code = yes

  saysNo_correct :
    ∀ code : F.Code, F.RealizedTrue (SaysNoClaim code) ↔ T.verdict code = no

/--
**Strongly self-scoped**: extends SelfScoped with the ability to encode
"T is wrong on code" — i.e. T says yes but claim is false, or T says no but claim is true.

This makes the diagonal/liar construction more direct.
-/
structure StronglySelfScoped extends SelfScoped F T where
  WrongClaim : F.Code → F.Claim

  wrong_correct :
    ∀ code : F.Code,
      F.RealizedTrue (WrongClaim code) ↔
        ((T.verdict code = yes ∧ ¬ F.selfSemanticTruth code) ∨
         (T.verdict code = no  ∧ F.selfSemanticTruth code))

end SemanticSelfDescription
