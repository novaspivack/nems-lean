# SurvivorCalculus — Program III Overview

**Formalization Agenda:** Survivor Calculus / Admissibility Cascade (from new_targets.tex)

## Purpose
Formalize the admissibility cascade where candidate spaces are filtered by closure-compatibility, survivor-compatibility, and further structured admissibility classes.

## Modules

| Module | Description |
|--------|-------------|
| Core/Cascade | Cascade, ResidualClass, InResidual |
| Theorems/MonotoneFiltering | residual_inclusion: R_{k+1} ⊆ R_k |
| Bridges/ToFoundationalAdmissibility | Bridge to NemS Cosmology (scaffold) |

## Main Theorems
- **residual_inclusion:** If x satisfies the first (k+1) constraints, it satisfies the first k.

## Build
`lake build SurvivorCalculus`
