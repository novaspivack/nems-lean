# Hypercomputation — Overview

**Paper 35: Oracles as External Selectors — NEMS Constraints on Hypercomputation and Physical Computability**

## Scope

The Hypercomputation library is a **thin, theorem-focused** wrapper over existing Closure, SelectorStrength, and NemS diagonal machinery. It formalizes:

1. **Oracle-as-selector audit** — any predicate decidable on world-types must be invariant; non-invariant predicates require external selection.
2. **No internal hypercomputer theorem** — under anti-decider closure and the fixed-point premise, no total internal decider exists for extensional nontrivial predicates.
3. **Five-regime taxonomy** — any purported internal hypercomputer claim forces failure of at least one barrier premise (diagonal, extensionality, nontriviality, or totality).

The library **does not** formalize:
- Full oracle Turing machines
- Malament–Hogarth spacetimes, CTCs, or black-hole physics
- Every exotic hypercomputation proposal individually

It formalizes the abstract closure/selector-strength constraint they must answer to.

## Dependencies

- `Closure` — ObsSemantics, audit soundness, DecidableOnWorldType
- `SelectorStrength` — Strength, DecidableAt, Extensional, Nontrivial, AntiDeciderClosed, barrier schema
- `NemS.Diagonal` — Halting framework, ASR, record-truth, no_total_effective_rt_decider

## Core definitions

| File | Definition | Description |
|------|------------|-------------|
| `Core/OracleAsSelector.lean` | `AuditPassesFor`, `SelectorSensitive` | Oracle-as-selector audit vocabulary |
| `Core/HypercomputerClaim.lean` | `HypercomputerClaim`, `HasInternalHypercomputerAt` | Hypercomputer claim interface |
| `Core/Taxonomy.lean` | `FailsDiagonalPremise`, `FailsExtensionality`, `FailsNontriviality` | Five failure-mode predicates |

## Flagship theorems

| File | Theorem | Statement |
|------|----------|-----------|
| `Theorems/NoInternalHypercomputer.lean` | `no_internal_hypercomputer_at_strength` | Under AntiDeciderClosed + hFP, no total internal hypercomputer for extensional nontrivial T |
| `Theorems/OracleAudit.lean` | `oracle_claim_requires_invariance` | DecidableOnWorldType ⇒ Invariant |
| `Theorems/OracleAudit.lean` | `selector_sensitive_not_decidable_on_world_type` | SelectorSensitive ⇒ ¬ DecidableOnWorldType |
| `Theorems/Taxonomy.lean` | `internal_hypercomputer_claim_forces_premise_failure` | HasInternalHypercomputerAt ⇒ at least one premise fails |

## Examples

| File | Theorem | Statement |
|------|----------|-----------|
| `Examples/Halting.lean` | `no_internal_hypercomputer_for_halting` | No computable total decider for halts-on-zero |
| `Examples/RecordTruth.lean` | `no_internal_hypercomputer_for_record_truth` | ASR ⇒ ¬ ComputablePred RT |

## Relation to Paper 35

- **Theorem 1 (Oracle-as-Selector):** `oracle_claim_requires_invariance`, `selector_sensitive_not_decidable_on_world_type`
- **Theorem 2 (No Internal Hypercomputer):** `no_internal_hypercomputer_at_strength`, `no_total_internal_hypercomputer`
- **Theorem 3 (Taxonomy):** `internal_hypercomputer_claim_forces_premise_failure`, `hypercomputation_taxonomy`
- **Examples:** `no_internal_hypercomputer_for_halting`, `no_internal_hypercomputer_for_record_truth`

## Relation to downstream papers

- **Paper 27 (Closure):** Reuses `audit_soundness`, `DecidableOnWorldType`, `Invariant`
- **Paper 29 (SelectorStrength):** Reuses `no_total_decider_at_strength_nontrivial`, barrier schema
- **Papers 36–38:** Taxonomy serves as audit checklist for chronology, black holes

## Sorry status

**0 sorry**, 0 custom axioms. All proofs are machine-checked wrappers over existing Closure and SelectorStrength machinery.

## Build

```bash
# From nems-lean root:
lake build Hypercomputation
```

Or full build:

```bash
lake build
```
