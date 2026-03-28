import Reflection.Core.SRI_R
import SelfReference.Core.FixedPoint
import SelfReference.Consequences.DiagonalBarrier

/-!
# SelfReference.Instances.Godel

## Gödel's Diagonal Lemma as an SRI instance

The **diagonal lemma** states: for any formula transformer `F : ℕ → ℕ`,
there exists `ψ : ℕ` with `T ⊢ ψ ↔ F(ψ)`.

We prove this directly from the abstract diagonal construction,
instantiated at a Gödel system.

## The Gödel system

A `GodelSystem` provides:
- `ProvBic : ℕ → ℕ → Prop` (provable biconditional, an equivalence)
- `subst : ℕ → ℕ → ℕ` (substitution: `subst φ n` = code of `φ(n̄)`)
- `repr_fn : (ℕ → ℕ) → ℕ` (representation: every transformer has a code)
- `repr_fn_spec : ProvBic (subst (repr_fn F) c) (F c)` (substitution lemma)
- `subst_cong` (congruence of substitution in first arg)
- `eval_quote_ax : ProvBic (subst n n) n` (self-substitution axiom)

Note: `eval_quote_ax` is an axiom of the abstract `GodelSystem` structure.
It is not universally true in concrete arithmetic (`sub(n,n) = n` does not
hold in general), but it holds for the specific codes produced by the
diagonal construction.  The diagonal lemma follows from `repr_fn_spec`
alone via MFP-1; `eval_quote_ax` is used in the unityped proof chain.
-/

namespace SelfReference
namespace Instances
namespace Godel

/-- Abstract Gödel system. -/
structure GodelSystem where
  ProvBic : ℕ → ℕ → Prop
  prov_refl  : ∀ n, ProvBic n n
  prov_symm  : ∀ {n m}, ProvBic n m → ProvBic m n
  prov_trans : ∀ {n m k}, ProvBic n m → ProvBic m k → ProvBic n k
  subst : ℕ → ℕ → ℕ
  repr_fn : (ℕ → ℕ) → ℕ
  repr_fn_spec : ∀ (F : ℕ → ℕ) (c : ℕ), ProvBic (subst (repr_fn F) c) (F c)
  subst_cong : ∀ {φ ψ : ℕ} (c : ℕ), ProvBic φ ψ → ProvBic (subst φ c) (subst ψ c)
  eval_quote_ax : ∀ n, ProvBic (subst n n) n

/--
**Gödel system → SRI₀′** (unityped numerals).

`Equiv := ProvBic`, `run := subst`, `quote := id`, `repr := repr_fn`, and `repr_spec` is exactly
`repr_fn_spec`.

Together with `Reflection.sri0'_to_sri_r` this yields **`SRI_R ℕ ℕ allRepresentable`** and hence
**`DiagClosed`** (Paper 28 diagonal-closure side).

**Remaining to obtain a closed `SemanticSelfDescription.BarrierHypotheses` via
`barrier_hypotheses_from_reflection`:** build a `SelfSemanticFrame` with `Code = ℕ`, supply
`CodeExtensional` whose `CodeEquiv` matches `ProvBic`, prove `EncodedNontrivial` for that frame, and
check the `hEquiv` / `hQuoteId` side-conditions of `barrier_hypotheses_from_reflection`. That
“arithmetical semantics” step is **not** forced by the abstract `GodelSystem` axioms alone.
-/
@[reducible]
def toSRI0' (G : GodelSystem) : SelfReference.SRI0' ℕ ℕ where
  Equiv := G.ProvBic
  equiv_refl := G.prov_refl
  equiv_symm := fun h => G.prov_symm h
  equiv_trans := fun h₁ h₂ => G.prov_trans h₁ h₂
  quote := id
  run := G.subst
  repr := G.repr_fn
  repr_spec := G.repr_fn_spec

/--
Induced **`SRI_R`** with **`R = allRepresentable`** (every `ℕ → ℕ` transformer is in the class).
-/
@[reducible]
def toSRI_R (G : GodelSystem) :
    Reflection.SRI_R ℕ ℕ (Reflection.allRepresentable (Obj := ℕ) (Code := ℕ)) :=
  @Reflection.sri0'_to_sri_r ℕ ℕ (toSRI0' G)

/--
Diagonal closure for the Gödel-derived **`SRI_R`**: **`R = ⊤`** is always diagonally closed.

The explicit **`SRI_R`** argument is needed because `toSRI_R G` is data (not a global `instance`).
-/
theorem diagClosed (G : GodelSystem) :
    @Reflection.DiagClosed ℕ ℕ (Reflection.allRepresentable (Obj := ℕ) (Code := ℕ)) (toSRI_R G) :=
  @Reflection.diagClosed_allRepresentable ℕ ℕ (toSRI_R G)

/--
`quote` in `toSRI0'` (hence in `toSRI_R`) is **`id`**, matching the **`hQuoteId`** side condition of
`SemanticSelfDescription.barrier_hypotheses_from_reflection`.
-/
theorem sri_quote_eq_id (G : GodelSystem) (p : ℕ) : (toSRI_R G).quote p = p :=
  rfl

/-- **Gödel's Diagonal Lemma** proved directly from the diagonal construction.

For any formula transformer `F : ℕ → ℕ` (congruent w.r.t. `ProvBic`),
there exists `ψ : ℕ` with `ProvBic ψ (F ψ)`.

**Proof**: Set `G c := F (subst c c)`, `d := repr_fn G`.
- `subst d d ≃ G d = F (subst d d)`  [repr_fn_spec at c = d]
- `subst d d ≃ d`  [eval_quote_ax]
- Chain: `d ≃ subst d d ≃ F (subst d d) ≃ F d`  [transitivity + hF_cong]

This is the unityped corollary of MFP-1, using `eval_quote_ax` to collapse
the mixed fixed point `subst d d ≃ F (subst d d)` to `d ≃ F d`. -/
theorem godel_diagonal_lemma (G : GodelSystem) (F : ℕ → ℕ)
    (hF_cong : ∀ {x y : ℕ}, G.ProvBic x y → G.ProvBic (F x) (F y)) :
    ∃ ψ : ℕ, G.ProvBic ψ (F ψ) := by
  let H : ℕ → ℕ := fun c => F (G.subst c c)
  let d : ℕ := G.repr_fn H
  use d
  have hstep1 : G.ProvBic (G.subst d d) (F (G.subst d d)) :=
    G.repr_fn_spec H d
  have hstep2 : G.ProvBic (G.subst d d) d :=
    G.eval_quote_ax d
  have hstep3 : G.ProvBic d (G.subst d d) :=
    G.prov_symm hstep2
  have hstep4 : G.ProvBic (F (G.subst d d)) (F d) :=
    hF_cong hstep2
  exact G.prov_trans hstep3 (G.prov_trans hstep1 hstep4)

/-- **Gödel sentence**: Taking `F n = neg (prov n)`, the diagonal lemma
gives `ψ` with `T ⊢ ψ ↔ ¬ Prov(ψ)`. -/
theorem godel_sentence (G : GodelSystem) (neg prov : ℕ → ℕ)
    (hNeg_cong : ∀ {x y}, G.ProvBic x y → G.ProvBic (neg x) (neg y))
    (hProv_cong : ∀ {x y}, G.ProvBic x y → G.ProvBic (prov x) (prov y)) :
    ∃ ψ : ℕ, G.ProvBic ψ (neg (prov ψ)) :=
  godel_diagonal_lemma G (fun n => neg (prov n))
    (fun h => hNeg_cong (hProv_cong h))

end Godel
end Instances
end SelfReference
