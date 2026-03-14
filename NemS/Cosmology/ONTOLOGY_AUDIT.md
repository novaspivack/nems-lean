# Ontology Audit: Unified Closure Framework

**Purpose:** Extract minimum primitives from SemanticFloor, ArrowOfTime, and NEMS/MFRR for building UnifiedClosureFramework.

## 1. SemanticFloor (CosmologicalFramework)

**Structure:** `CosmologicalFramework extends Framework`
- Framework: `Model`, `Rec`, `Truth : Model → Rec → Prop`
- CosmologicalFramework adds: `InitState : Type`, `init : InitState`
- Continuations = Model
- Needs: `[DiagonalCapable F.toFramework]`, `(U : Universe F.toFramework)`, `Nonempty (PSCBundle F (fun _ => True))` for full theorems
- Key theorem: `semantic_floor F U` gives `F.SatisfiesSemanticFloor`

**Primitives required:** Model, Rec, Truth, InitState, init

## 2. ArrowOfTime (RecordFiltration)

**Structure:** `RecordFiltration World Obs extends Closure.ObsSemantics World Obs`
- ObsSemantics: `Holds : World → Obs → Prop`
- RecordFiltration adds: `Visible : Time → Obs → Prop`, `mono` (t ≤ t' → Visible t o → Visible t' o)
- Time = Nat
- ObsEqAt, WorldTypeAt, forget (all derivable from Holds + Visible + mono)

**Primitives required:** World, Obs (≈ Rec), Holds (≈ Truth), Visible, mono

**Overlap with 1:** World = Model, Obs = Rec, Holds = Truth

## 3. NEMS/MFRR (Framework)

**Framework** (from Basics, ObsEq, Categoricity, Selectors):
- Model, Rec, Truth
- ObsEq := ∀ r, Truth M r ↔ Truth N r
- WorldTypes := Quotient ObsEq
- Selector, ObsCategorical, NeedsExternalSelection, NEMS, PSCBundle

**Bridge theorems (BridgeToNEMS):**
- `no_external_law`: PSCBundle F IsInternal → ¬ NeedsExternalSelection F IsInternal
- `PSC_and_choice_force_PT`, `PSC_choice_diagonal_forces_constrained_selection`

**Primitives required:** Model, Rec, Truth (same as Framework)
- ChoiceData, HasRecordDivergentChoice for choice-based results
- PSCBundle bundles NEMS + DeterminacyPSC

## 4. Overlapping notions

| Concept   | SemanticFloor     | ArrowOfTime      | NEMS Framework   |
|----------|-------------------|------------------|------------------|
| Realizations | Model          | World            | Model            |
| Records  | Rec               | Obs              | Rec              |
| Satisfaction | Truth          | Holds            | Truth            |
| Equivalence | (from Framework) | ObsEqAt (stage)  | ObsEq (global)   |

**Key alignment:** World = Model, Obs = Rec, Holds = Truth. ArrowOfTime adds time-indexed visibility.

## 5. Mismatched notions

- **ReflexiveTheorySpace** (Finality): Theory, K, RecordEquivalent, MetaExplanation, etc. — different ontology (theory space, not model space). Bridge to Finality is harder; spec recommends using ¬NeedsExternalSelection for summit, then corollary for outside_dependence_exhaustion.
- **Universe** (ExecutionNecessity): State, PT. Required for semantic_floor theorem. Can be assumed Nonempty in schema.

## 6. Candidate common primitives

```
World : Type u       -- models/realizations
Rec : Type v         -- records/observations
Truth : World → Rec → Prop
InitState : Type w
init : InitState
Visible : Nat → Rec → Prop  -- stage visibility
visible_mono : ∀ t t' r, t ≤ t' → Visible t r → Visible t' r
```

This minimal set suffices to interpret all three ontologies.
