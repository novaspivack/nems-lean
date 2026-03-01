# nems-lean v2.0.0 — Artifact Manifest

**Release:** v2.0.0  
**Date:** February 2026  
**Lean version:** leanprover/lean4:v4.28.0  
**Mathlib version:** v4.28.0  
**Build result:** 8062 jobs, 0 errors, **1 `sorry`** (see below), **zero custom axioms**

### Sorry status

One `sorry` remains in `NemS/Quantum/BuschGleason.lean`: the **existence** direction of the Busch/Gleason
representation theorem (`busch_gleason`). This is the deep result that for any normalized,
POVM-additive probability assignment μ on quantum effects, *there exists* a density operator ρ
such that μ(E) = Re(Tr(ρE)) for all effects E.

This result is mathematically well-established (Gleason 1957; Busch 1999) and is not in
scientific dispute. It requires a linear-extension argument on the finite-dimensional Hermitian
space Herm(n) — specifically showing POVM-additivity implies linearity — which goes beyond the
matrix-computation infrastructure currently in this library.

All other theorems in the library are fully proved without `sorry`, including:
- **Uniqueness**: `busch_gleason_unique` — if any ρ represents μ, it must be the unique one (0 sorrys)
- The full diagonal barrier, physical incompleteness, and determinism no-go chains (0 sorrys)
- The complete NEMS core, MFRR bridge, and test-effect infrastructure (0 sorrys)

## Verified theorems

### Core (v1.0.0)

| File | Theorem | Statement |
|------|---------|-----------|
| `NemS/Core/Trichotomy.lean` | `nems_trichotomy` | Categorical ∨ internal selector ∨ needs external selection |
| `NemS/Core/Trichotomy.lean` | `nems_implies_cat_or_internal` | NEMS ⇒ categorical ∨ internal selector |
| `NemS/Core/Trichotomy.lean` | `nems_noncat_implies_internal` | NEMS + non-categorical ⇒ internal selector |
| `NemS/Reduction/ER.lean` | `er_non_categorical` | External dependency ⇒ non-categoricity in enlarged space |
| `NemS/Reduction/ER.lean` | `er_nems_forces_internal_selector` | NEMS on enlarged space ⇒ internal selector |
| `NemS/Reduction/ER.lean` | `nems_er_implies_detpsc` | NEMS + ER ⇒ determinacy-PSC |
| `NemS/Visibility/SemanticExternality.lean` | `semantic_externality_not_categorical` | Semantic externality ⇒ non-categoricity in F⁺ |
| `NemS/Visibility/SemanticExternality.lean` | `nems_forces_evaluator_selector` | NEMS forces internal selector for evaluator choices |
| `NemS/Meta/AuditProtocol.lean` | `passAudit_iff_nems` | PassAudit ↔ NEMS |
| `NemS/Core/Internality.lean` | `nems_definability` | NEMS under definability-internality |
| `NemS/Core/Internality.lean` | `nems_computability` | NEMS under computability-internality |
| `NemS/Core/Internality.lean` | `definability_implies_quotient_section` | Definability ⇒ quotient section exists |

### Diagonal Barrier (v2.0.0)

| File | Theorem | Statement |
|------|---------|-----------|
| `NemS/Diagonal/HaltingReduction.lean` | `asr_rt_computable_implies_halting_computable` | ASR + computable RT ⇒ computable halting |
| `NemS/Diagonal/HaltingReduction.lean` | `asr_rt_not_computable` | **ASR ⇒ RT not computable (diagonal barrier, Thm 5.9)** |
| `NemS/Diagonal/Barrier.lean` | `no_total_effective_rt_decider` | ASR ⇒ ¬ ComputablePred RT |
| `NemS/Diagonal/Instantiation.lean` | `halting_framework_rt_not_computable` | Concrete instantiation recovers halting undecidability |

### MFRR Bridge (v2.0.0)

| File | Theorem | Statement |
|------|---------|-----------|
| `NemS/MFRR/ChoicePoints.lean` | `recordDivergentChoice_implies_not_obsCategorical` | Record-divergent choice ⇒ non-categoricity |
| `NemS/MFRR/ChoicePoints.lean` | `recordDivergentChoice_witness` | Extract disagreeing models from choice data |
| `NemS/MFRR/PSCBundle.lean` | `PSCBundle.cat_or_internal` | PSC ⇒ categorical ∨ internal selector |
| `NemS/MFRR/PTSelector.lean` | `nems_noncat_forces_PT` | NEMS + non-categorical ⇒ PT exists |
| `NemS/MFRR/PTSelector.lean` | `nems_cat_or_PT` | NEMS ⇒ categorical ∨ PT exists |
| `NemS/MFRR/DiagonalBarrier.lean` | `diagonal_barrier_rt` | **Diagonal-capable ⇒ RT not computable (zero axioms)** |
| `NemS/MFRR/DiagonalBarrier.lean` | `nems_noncat_forces_internal_and_diagonal_barrier` | NEMS + non-cat + diagonal ⇒ selector + undecidable RT |
| `NemS/MFRR/BridgeToNEMS.lean` | `PSC_and_choice_force_PT` | **PSC + record-divergent choice ⇒ PT exists** |
| `NemS/MFRR/BridgeToNEMS.lean` | `PSC_choice_diagonal_forces_constrained_selection` | **PSC + choice + diagonal ⇒ selector + undecidable RT** |
| `NemS/MFRR/BridgeToNEMS.lean` | `PSC_classification` | PSC + diagonal ⇒ categorical ∨ (selector ∧ undecidable RT) |
| `NemS/MFRR/BridgeToNEMS.lean` | `no_external_law` | PSC ⇒ ¬ NeedsExternalSelection |
| `NemS/MFRR/PTNonEffective.lean` | `pt_not_total_effective_on_RT` | **Diagonal-capable ⇒ PT not total-effective on RT** |
| `NemS/MFRR/PTNonEffective.lean` | `pt_exists_and_not_effective` | NEMS + non-cat + diagonal ⇒ ∃ PT, ¬ effective |
| `NemS/MFRR/ToyMFRR.lean` | `bool_PT_exists` | Bool framework: PT extracted via bridge theorem |
| `NemS/MFRR/ToyMFRR.lean` | `bool_has_divergent_choice` | Bool framework has record-divergent choice |

## Key source files (SHA-256)

To verify integrity, compute `sha256sum` on the following files and compare:

```
NemS.lean
NemS/Prelude.lean
NemS/Core/Basics.lean
NemS/Core/ObsEq.lean
NemS/Core/Categoricity.lean
NemS/Core/Selectors.lean
NemS/Core/Trichotomy.lean
NemS/Core/Internality.lean
NemS/Reduction/Externality.lean
NemS/Reduction/EnlargedSpace.lean
NemS/Reduction/ER.lean
NemS/Visibility/Recordability.lean
NemS/Visibility/SelfEncoding.lean
NemS/Visibility/SemanticExternality.lean
NemS/Diagonal/ASR.lean
NemS/Diagonal/HaltingReduction.lean
NemS/Diagonal/Barrier.lean
NemS/Diagonal/Instantiation.lean
NemS/MFRR/ChoicePoints.lean
NemS/MFRR/PSCBundle.lean
NemS/MFRR/PTSelector.lean
NemS/MFRR/DiagonalBarrier.lean
NemS/MFRR/BridgeToNEMS.lean
NemS/MFRR/PTNonEffective.lean
NemS/MFRR/ToyMFRR.lean
NemS/Examples/Toy.lean
NemS/Meta/AuditProtocol.lean
lakefile.lean
lean-toolchain
```

## Reproduction

```bash
# From a clean checkout of this repository at tag v2.0.0:
lake update    # fetches Mathlib (cached oleans downloaded automatically)
lake build     # compiles the full library
```

Expected output: `Build completed successfully (8052 jobs).`

## What is axiomatized vs. proved

### Core
- **Axiomatized:** `Framework` (Model, Rec, Truth); `IsInternal` predicate (abstract parameter)
- **Proved:** all implication structure (Trichotomy, ER, determinacy-PSC, semantic visibility, audit equivalence)
- **Two instantiations provided:** definability-style and computability-style internality

### Diagonal Barrier
- **Axiomatized:** nothing (zero custom axioms)
- **Proved:** ASR ⇒ record-truth not computable, via reduction to Mathlib's `ComputablePred.halting_problem`
- **Concrete instantiation:** halting framework demonstrates ASR is satisfiable

### MFRR Bridge
- **Axiomatized:** nothing (zero custom axioms)
- **Proved:** choice points ⇒ non-categoricity; PSC + choice ⇒ PT exists; PSC + choice + diagonal ⇒ constrained selection; PSC classification; no external law
- **Toy instantiation:** Bool framework with record-divergent choice, PSC bundle, and PT extraction

### Summary: the entire library has **zero custom axioms** beyond Lean's kernel axioms.

## Companion papers

This artifact formalizes the core spine of:
- *Semantic Closure Under No External Model Selection* (NEMS Theorem paper)
- *The NEMS Framework* (overview document)
- *From NEMS to MFRR: A Machine-Checked Bridge* (Paper 21)
