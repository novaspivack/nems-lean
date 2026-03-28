import Reflection.Core.SRI_R
import Reflection.Theorems.DiagonalClosure
import SemanticSelfDescription.Core.Claims
import SemanticSelfDescription.Theorems.NoFinalSelfTheory

/-!
# SemanticSelfDescription.Bridge.ToReflection

**Bridge: DiagClosed R supplies the fixed-point premise for BarrierHypotheses.**

When the frame's Code carries SRI_R with DiagClosed R (e.g. from SelfReference
when Obj = Code), and CodeExtensional's CodeEquiv matches SRI Equiv, the
fixed-point premise hFP required by BarrierHypotheses is supplied by Reflection's
restricted_master_fixed_point.

This completes the chain: Reflection (DiagClosed) → BarrierHypotheses → no_final_self_theory.

## Gödel systems → **the same** reflection side (numeral **`Code = ℕ`**)

Every abstract `SelfReference.Instances.Godel.GodelSystem` yields `toSRI0'`, `toSRI_R`, and
`Godel.diagClosed` on `ℕ`, with `quote = id` (`Godel.sri_quote_eq_id`). That is exactly the
`SRI_R` / `DiagClosed` / `hQuoteId` input pattern expected by `reflection_supplies_hFP` and
`barrier_hypotheses_from_reflection` once you also provide a semantic frame `F` with `F.Code = ℕ`,
`CodeExtensional` whose `CodeEquiv` matches the same `ProvBic`, and `[EncodedNontrivial F]`.
The latter “arithmetical semantics” bundle is **not** forced by the abstract `GodelSystem` axioms
alone; see `SelfReference/Instances/Godel.lean` for the honest scaffolding / remainder note.

## Sharp obstructions (why “pick `Code = ℕ`” is not automatic)

* `SemanticSelfDescription.false_of_encodedNontrivial_indiscrete_CodeEquiv` — if **every** code pair is
  `CodeEquiv`, then `EncodedNontrivial` is false.
* `SemanticSelfDescription.false_of_encodedNontrivial_aligns_univ` — same packaging when `CodeEquiv`
  is aligned with a **universal** binary relation (e.g. `ProvBic := fun _ _ => True`).
* `SelfReference.Minimality.not_nonempty_sri0'_nat_equiv_eq` — **no** unityped `SRI₀′` on `ℕ` has
  `Equiv` **coincide** with `Eq`, so you cannot align `CodeEquiv` with **equality** *and* use this
  reflection/representability chain at **`R = ⊤`**.

Closing a **parameter-free** `bh` via `barrier_hypotheses_from_reflection` therefore needs a
**concrete** intermediate equivalence (proof-theoretic `ProvBic`, Kleene-style `ExtEq`, …)—**strictly
between** `Eq` and the universal relation—together with an **`EncodedNontrivial`** **witness** for
`RealizedTrue` invariant under **that** equivalence, **and** a **concrete** `GodelSystem` /
`ProgramSystem`-style witness for `run`/`repr`, not the abstract shell alone.
-/

set_option autoImplicit false

namespace SemanticSelfDescription

universe u v

variable {W : Type u} (F : SelfSemanticFrame W)

/--
**Reflection supplies BarrierHypotheses.hFP.**

When:
- The frame's Code has SRI_R with diagonally closed R (all F' representable)
- CodeExtensional's CodeEquiv coincides with SRI_R.Equiv
- quote is identity (unityped setting: F(quote p) = F p)

then for every F' : F.Code → F.Code, Reflection gives a fixed point d with
CodeEquiv d (F' d), yielding the hFP premise for BarrierHypotheses.
-/
theorem reflection_supplies_hFP
    (codeExt : CodeExtensional F)
    (R : (F.Code → F.Code) → Prop)
    [sri : Reflection.SRI_R F.Code F.Code R]
    (hDiag : Reflection.DiagClosed R)
    (hEquiv : ∀ a b, codeExt.CodeEquiv a b ↔ sri.Equiv a b)
    (hR : ∀ F' : F.Code → F.Code, R F')
    (hQuoteId : ∀ p : F.Code, sri.quote p = p) :
    ∀ F' : F.Code → F.Code, ∃ d : F.Code, codeExt.CodeEquiv d (F' d) := by
  intro F'
  obtain ⟨p, hp⟩ := Reflection.restricted_master_fixed_point hDiag F' (hR F')
  use p
  have hp' : sri.Equiv p (F' p) := by rw [hQuoteId p] at hp; exact hp
  exact (hEquiv p (F' p)).mpr hp'

/--
**BarrierHypotheses from Reflection.**

When the frame has code extensionality, encoded nontriviality, and the
Reflection setup above (SRI_R on Code with DiagClosed, CodeEquiv = Equiv,
quote = id), we obtain full BarrierHypotheses and thus no_final_self_theory.
-/
def barrier_hypotheses_from_reflection
    (codeExt : CodeExtensional F)
    [EncodedNontrivial F]
    (R : (F.Code → F.Code) → Prop)
    [sri : Reflection.SRI_R F.Code F.Code R]
    (hDiag : Reflection.DiagClosed R)
    (hEquiv : ∀ a b, codeExt.CodeEquiv a b ↔ sri.Equiv a b)
    (hR : ∀ F' : F.Code → F.Code, R F')
    (hQuoteId : ∀ p : F.Code, sri.quote p = p) :
    BarrierHypotheses F :=
  ⟨codeExt, inferInstance, reflection_supplies_hFP F codeExt R hDiag hEquiv hR hQuoteId⟩

/--
If `CodeEquiv` is **aligned** with a relation `Rel` that holds for **all** code pairs (“universal” /
indiscrete side), then **`EncodedNontrivial`** cannot hold — cf. induced `ProvBic := fun _ _ => True`
Gödel shells once `hEquiv` forces `CodeEquiv` from `ProvBic`.
-/
theorem false_of_encodedNontrivial_aligns_univ
    {W : Type u} (F : SelfSemanticFrame W) (codeExt : CodeExtensional F) [EncodedNontrivial F]
    (Rel : F.Code → F.Code → Prop)
    (hEquiv : ∀ a b, codeExt.CodeEquiv a b ↔ Rel a b)
    (hUniv : ∀ a b, Rel a b) : False :=
  false_of_encodedNontrivial_indiscrete_CodeEquiv F codeExt fun a b => (hEquiv a b).mpr (hUniv a b)

end SemanticSelfDescription
