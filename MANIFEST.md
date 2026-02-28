# nems-lean v1.0.0 — Artifact Manifest

**Release:** v1.0.0  
**Date:** February 2026  
**Lean version:** leanprover/lean4:v4.28.0  
**Mathlib version:** v4.28.0  
**Build result:** 8041 jobs, 0 errors, zero `sorry`

## Verified theorems

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
NemS/Examples/Toy.lean
NemS/Meta/AuditProtocol.lean
lakefile.lean
lean-toolchain
```

## Reproduction

```bash
# From a clean checkout of this repository at tag v1.0.0:
lake update    # fetches Mathlib (cached oleans downloaded automatically)
lake build     # compiles the full library
```

Expected output: `Build completed successfully (8041 jobs).`

## What is axiomatized vs. proved

- **Axiomatized:** `Framework` (Model, Rec, Truth); `IsInternal` predicate (abstract)
- **Proved:** all implication structure (Trichotomy, ER, determinacy-PSC, semantic visibility, audit equivalence)
- **Two instantiations provided:** definability-style and computability-style internality

## Companion papers

This artifact formalizes the core spine of:
- *Semantic Closure Under No External Model Selection* (NEMS Theorem paper)
- *The NEMS Framework* (overview document)
