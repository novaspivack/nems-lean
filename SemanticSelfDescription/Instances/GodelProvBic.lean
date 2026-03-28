import Reflection.Core.SRI_R
import SemanticSelfDescription.Core.Claims
import SemanticSelfDescription.Bridge.ToReflection
import SelfReference.Instances.Godel

/-!
# SemanticSelfDescription.Instances.GodelProvBic

**Proof-theoretic (`ProvBic`) self-semantic frame and `BarrierHypotheses` from reflection.**

An abstract `SelfReference.Instances.Godel.GodelSystem` yields diagonal / representability
machinery (`toSRI_R`, `diagClosed`, `quote = id`) but **does not** determine realized truth on codes.

**`ProvBicArithmeticalSemantics`** packages exactly the extra “arithmetical semantics” input called out
in `SelfReference/Instances/Godel.lean`: a predicate on `ℕ` that respects `ProvBic` and is
**encoded-nontrivial**.

With that, we build `godelProvBicFrame`, prove `EncodedNontrivial` and `CodeExtensional`, and obtain
full **`BarrierHypotheses`** via `barrier_hypotheses_from_reflection`.

**Contrast:** the predicated Kleene / computability summit (**SPEC_019_PS1**, `KleenePredicatedSummit`) stays
the **frozen** baseline for **`BarrierHypothesesPred`**; this module is the honest **`BarrierHypotheses`**
closure point for the **`ProvBic`** / proof-theoretic route (**SPEC_020_PT1** / **EPIC_013**).
-/

set_option autoImplicit false

namespace SemanticSelfDescription

open SelfReference.Instances

/-- Data for **realized truth** on numerals, layered on `Godel.GodelSystem`, invariant under `ProvBic`
and **nontrivial on codes** (so `EncodedNontrivial` holds). -/
structure ProvBicArithmeticalSemantics (G : Godel.GodelSystem) where
  realizes : ℕ → Prop
  realizes_ext : ∀ {c₁ c₂ : ℕ}, G.ProvBic c₁ c₂ → (realizes c₁ ↔ realizes c₂)
  codeTrue : ℕ
  codeFalse : ℕ
  realizes_true : realizes codeTrue
  realizes_false : ¬ realizes codeFalse

/-- Unityped frame: **`Code = Claim = ℕ`**, **`decode = id`**, claim equivalence **`G.ProvBic`**. -/
def godelProvBicFrame (G : Godel.GodelSystem) (_S : ProvBicArithmeticalSemantics G) :
    SelfSemanticFrame Unit where
  Code := ℕ
  Claim := ℕ
  decode := id
  RealizedTrue := _S.realizes
  ClaimEquiv := G.ProvBic
  truth_ext := fun {_ _} h => _S.realizes_ext h

/-- Encoded nontriviality from the semantics witness. -/
instance godelProvBic_encodedNontrivial (G : Godel.GodelSystem) (S : ProvBicArithmeticalSemantics G) :
    EncodedNontrivial (godelProvBicFrame G S) where
  code_true := ⟨S.codeTrue, by
    simp only [SelfSemanticFrame.selfSemanticTruth, godelProvBicFrame]
    rw [id]
    exact S.realizes_true⟩
  code_false := ⟨S.codeFalse, by
    simp only [SelfSemanticFrame.selfSemanticTruth, godelProvBicFrame]
    rw [id]
    exact S.realizes_false⟩

/-- Code extensionality aligned with **`ProvBic`** (middle equivalence on codes). -/
def godelProvBicCodeExtensional (G : Godel.GodelSystem) (S : ProvBicArithmeticalSemantics G) :
    CodeExtensional (godelProvBicFrame G S) where
  CodeEquiv := G.ProvBic
  decode_ext := fun {_ _} h => h

/--
**Full `BarrierHypotheses`** for a Gödel system plus explicit arithmetical semantics.

Uses `Godel.toSRI_R` / `diagClosed` / `sri_quote_eq_id` and
`barrier_hypotheses_from_reflection`.
-/
def godelProvBicBarrierHypotheses (G : Godel.GodelSystem) (S : ProvBicArithmeticalSemantics G) :
    BarrierHypotheses (godelProvBicFrame G S) :=
  @barrier_hypotheses_from_reflection
    Unit
    (godelProvBicFrame G S)
    (godelProvBicCodeExtensional G S)
    (godelProvBic_encodedNontrivial G S)
    (Reflection.allRepresentable (Obj := ℕ) (Code := ℕ))
    (Godel.toSRI_R G)
    (Godel.diagClosed G)
    (fun _ _ => Iff.rfl)
    (fun _ => trivial)
    (Godel.sri_quote_eq_id G)

end SemanticSelfDescription
