# nems-lean

**Lean 4 formalization of the NEMS (No External Model Selection) core spine.**

This library machine-checks the central theorems of the NEMS framework:
a formal criterion for what it means for a theory to be *fundamental*.

## What the library proves

### Phase 1 — Core (NemS.Core)

| Theorem | Statement |
|---------|-----------|
| `ObsEq.isEquivalence` | Record observational equivalence is an equivalence relation |
| `obsCategorical_iff_subsingleton` | Categoricity ↔ the world-type quotient is a subsingleton |
| `nems_trichotomy` | For any framework: categorical ∨ internal selector ∨ needs external selection |
| `nems_implies_cat_or_internal` | **NEMS ⇒ categorical ∨ internal selector** (the "no outsourcing meaning" theorem) |

### Phase 2 — Externality Reduction (NemS.Reduction)

| Theorem | Statement |
|---------|-----------|
| `er_non_categorical` | Any nontrivial external dependency induces non-categoricity in the enlarged space |
| `er_nems_forces_internal_selector` | NEMS on the enlarged space forces an internal selector |
| `nems_er_implies_detpsc` | NEMS + ER ⇒ determinacy-PSC |

### Phase 3 — Semantic Visibility (NemS.Visibility)

| Theorem | Statement |
|---------|-----------|
| `distinct_evaluators_not_obsEq` | Distinct evaluator choices are record-distinguishable in F⁺ |
| `semantic_externality_not_categorical` | Semantic externalities induce non-categoricity in the self-encoding extension |
| `nems_forces_evaluator_selector` | NEMS forces an internal selector for evaluator choices |

### Meta — Audit Protocol (NemS.Meta)

| Definition/Theorem | Statement |
|-------------------|-----------|
| `PassAudit` | A framework passes the NEMS audit iff it is categorical or has an internal selector |
| `passAudit_iff_nems` | PassAudit ↔ NEMS |
| `fails_audit_not_fundamental` | Failing the audit = not fundamental in the NEMS sense |

## What "internal" means

The `IsInternal : Selector F → Prop` predicate is kept **abstract** throughout.
The library proves theorems parametric over any internality predicate.
Instantiating it with a specific notion (e.g., definability in a formal language,
computability, derivability from closure resources) is left to downstream work.

## What is NOT proven (Phase 1 scope)

- Full formal model theory (`⊨`) for first/second-order logic
- Physics-specific premises (record definiteness, physical universality)
- Computability/definability characterization of "internal"
- The diagonal barrier (Gödel/Kleene/Lawvere) — planned for a future module

## How to build

```bash
# Install elan (Lean version manager) if not already installed:
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y

# From the nems-lean/ directory:
lake update    # downloads Mathlib (takes ~5-10 min first time)
lake build     # compiles the library
```

## Repository structure

```
nems-lean/
  NemS.lean                        # root barrel (import all)
  NemS/
    Prelude.lean                   # common imports and options
    Core/
      Basics.lean                  # Framework structure
      ObsEq.lean                   # observational equivalence + Setoid
      Categoricity.lean            # ObsCategorical definition + lemmas
      Selectors.lean               # Selector structure + properties
      Trichotomy.lean              # NEMS Trichotomy + main corollary
    Reduction/
      Externality.lean             # ExternalDependency structure
      EnlargedSpace.lean           # enlarged framework construction
      ER.lean                      # Externality Reduction theorem
    Visibility/
      Recordability.lean           # evaluation-recordability predicate
      SelfEncoding.lean            # self-encoding extension F⁺
      SemanticExternality.lean     # semantic externality → record-visible
    Examples/
      Toy.lean                     # concrete toy instantiations
    Meta/
      AuditProtocol.lean           # NEMS Audit Protocol as Lean definition
```

## Relation to the paper suite

This library formalizes the spine of:

- *Semantic Closure Under No External Model Selection* (Semantic Closure paper)
- *The NEMS Framework* (overview document)

The theorems here correspond directly to:
- **Trichotomy** → `nems_trichotomy` + `nems_implies_cat_or_internal`
- **ER** → `er_non_categorical` + `er_nems_forces_internal_selector`
- **Semantic visibility** → `semantic_externality_not_categorical` + `nems_forces_evaluator_selector`

## License

MIT
