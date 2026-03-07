import SelectorStrength.Core.Deciders

/-!
# SemanticSelfDescription.Core.Claims

**Self-semantic claim families for a world (Necessary Incompleteness of Self-Description).**

A `SelfSemanticFrame` provides the vocabulary for claims about a world's own
realized semantics: internally representable codes, decoded claims, and the
actual realized truth predicate. This is the foundation for the theorem that
no universe can internally contain a final, faithful, complete theory of its
own realized semantics.

## Key definitions

- `SelfSemanticFrame W` : Code, Claim, decode, RealizedTrue
- `SelfSemanticTruth` : the predicate on codes (realized truth of decoded claim)
- `NontrivialFrame`, `EncodedNontrivial`, `CodeExtensional`
-/

set_option autoImplicit false

namespace SemanticSelfDescription

universe u v

variable (W : Type u)

/--
A **self-semantic frame** for a world `W` provides:
- `Code` : internally representable code-space of claims
- `Claim` : semantic objects expressed by those codes
- `decode` : turns internal codes into semantic claims
- `RealizedTrue` : the actual realized semantic truth predicate
- `ClaimEquiv` : extensional equality on claims (truth respects this)
-/
structure SelfSemanticFrame (W : Type u) where
  Code        : Type v
  Claim       : Type v
  decode      : Code → Claim
  RealizedTrue : Claim → Prop
  ClaimEquiv  : Claim → Claim → Prop

  /-- Claim-truth is extensional w.r.t. claim equivalence. -/
  truth_ext :
    ∀ {c₁ c₂ : Claim}, ClaimEquiv c₁ c₂ → (RealizedTrue c₁ ↔ RealizedTrue c₂)

/--
The **self-semantic truth** predicate on codes:
a code is "true" iff its decoded claim is realized-true in the world.
-/
def SelfSemanticFrame.selfSemanticTruth {W : Type u} (F : SelfSemanticFrame W) : F.Code → Prop :=
  fun code => F.RealizedTrue (F.decode code)

/--
**Nontrivial frame**: the claim family has both true and false instances.
Needed for barrier theorems.
-/
class NontrivialFrame {W : Type u} (F : SelfSemanticFrame W) : Prop where
  some_true  : ∃ c : F.Claim, F.RealizedTrue c
  some_false : ∃ c : F.Claim, ¬ F.RealizedTrue c

/--
**Encoded nontriviality**: the self-semantic truth predicate (on codes)
has both true and false instances. Stronger than NontrivialFrame when
not all claims are encodable.
-/
class EncodedNontrivial {W : Type u} (F : SelfSemanticFrame W) : Prop where
  code_true  : ∃ code : F.Code, F.selfSemanticTruth code
  code_false : ∃ code : F.Code, ¬ F.selfSemanticTruth code

/--
**Code extensionality**: an equivalence on codes such that equivalent codes
decode to equivalent claims. This makes self-semantic truth extensional.
-/
structure CodeExtensional {W : Type u} (F : SelfSemanticFrame W) where
  CodeEquiv : F.Code → F.Code → Prop
  decode_ext :
    ∀ {a b : F.Code}, CodeEquiv a b → F.ClaimEquiv (F.decode a) (F.decode b)

/--
When the frame has code extensionality, self-semantic truth is extensional
w.r.t. CodeEquiv.
-/
theorem selfSemanticTruth_extensional
    {W : Type u} (F : SelfSemanticFrame W) (ext : CodeExtensional F) :
    ∀ {a b : F.Code},
      ext.CodeEquiv a b →
      (F.selfSemanticTruth a ↔ F.selfSemanticTruth b) := by
  intro a b hab
  exact F.truth_ext (ext.decode_ext hab)

/--
EncodedNontrivial implies SelectorStrength.Nontrivial for self-semantic truth.
-/
theorem encodedNontrivial_implies_nontrivial
    {W : Type u} (F : SelfSemanticFrame W) [EncodedNontrivial F] :
    SelectorStrength.Nontrivial F.selfSemanticTruth :=
  ⟨EncodedNontrivial.code_true, EncodedNontrivial.code_false⟩

end SemanticSelfDescription
