# InternalitySchema — Program I Overview

**Formalization Agenda:** Internality / Outsourcing Schema (from new_targets.tex)

## Purpose
Package the NEMS pattern: if a task is load-bearing for determinacy and not internally realizable, then any completion depends on outsourced structure.

## Modules

| Module | Description |
|--------|-------------|
| Core/SystemTask | SystemTaskInterface: System, Task, Structure, LoadBearing, InternallyRealizable, CompletedBy, InternalTo |
| Theorems/OutsourcingBarrier | outsourcing_barrier, outsources_witness |
| Theorems/NEMSRecovery | nems_recovery: recovers NEMS trichotomy from schema |
| Instances/Closure | NEMSInterface, NEMSInterfaceFixed |

## Main Theorems
- **outsourcing_barrier:** LoadBearing ∧ ¬InternallyRealizable ∧ CompletedBy(s,t,x) ⇒ ¬InternalTo(x,s)
- **nems_recovery:** Non-categorical + no internal selector ⇒ any purported selector is non-internal

## Build
`lake build InternalitySchema`
