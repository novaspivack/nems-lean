/-!
# SelfReference — General Self-Reference Calculus

Root barrel file for the SelfReference library.

This library extracts the NEMS "record semantics + selection + diagonal
exposure" machinery into an **abstract interface** (the SRI'), proves a
**master fixed-point theorem** (MFP-1) and a **master diagonal barrier**
(MFP-2) once, then recovers Gödel, Kleene, Löb, and NEMS as instances.

## Design: the two-sorted SRI'

The interface is **two-sorted**: `SRI' Obj Code` separates the semantic
level (`Obj`) from the syntactic level (`Code`).  This is the correct
abstract form for all classical instances:

| Instance | `Obj`  | `Code` | `quote`     | `run e c`   |
|----------|--------|--------|-------------|-------------|
| Gödel    | `ℕ`    | `ℕ`    | numeral map | `sub(e, c)` |
| Kleene   | `ℕ`    | `ℕ`    | `id`        | `smn(e, c)` |
| NEMS     | `Prop` | `ℕ`    | record code | ASR eval    |
| Unityped | `α`    | `α`    | `id` (≃)    | application |

The unityped `SRI α` (with `Obj = Code = α`) is retained as an alias
for backward compatibility.

## Module structure

- `SelfReference.Core`         — The SRI' typeclass, representability,
                                  and the master fixed-point theorem.
- `SelfReference.Consequences` — The abstract diagonal barrier (MFP-2).
- `SelfReference.Instances`    — NEMS, Gödel, Kleene, Löb as instances.
- `SelfReference.Minimality`   — Countermodels and the stratification ladder.

## The key theorem (MFP-1)

`CSRI'.master_fixed_point`: In any `CSRI' Obj Code` system, for every
congruent transformer `F : Code → Obj`, there exists `p : Obj` with
`p ≃ F (quote p)`.

This is the **mixed fixed point**: `p` is an object that is semantically
equivalent to `F` applied to the code of `p`.

**Unityped corollary** (`CSRI.master_fixed_point`): In any `CSRI α`
system with `quote x ≃ x`, there exists `d : α` with `d ≃ F d`.

## The key corollary (MFP-2)

`Consequences.no_total_decider`: In any `CSRI` system, no extensional
nontrivial truth predicate has a total decider within the representable
class.

`Consequences.nems_rt_no_computable_bool_decider`: For computable
deciders, the result follows from `Nat.Partrec.Code.fixed_point`.

## The semantic trichotomy

`Minimality.semantic_trichotomy`: Every system is either
(1) Stratum 0 (no internalization, non-constant functions may have no
    fixed points — witnessed by `Bool`/`not`),
(2) Stratum 1 (partial internalization — witnessed by the
    constant-functions-only system on `ℕ`), or
(3) Stratum 2 (full internalization, diagonal barrier applies).

This corresponds to the NEMS Class I / IIa / IIb classification.

## Sorry count: 0

All theorems in this library are fully machine-checked.  The Löb
HBL chaining is proved using the `imp_intro` (deduction theorem) axiom
of `ProvSystem`.  The NEMS diagonal barrier is proved via
`Nat.Partrec.Code.fixed_point` (for computable deciders) and via the
halting reduction in `NemS.Diagonal.Barrier` (for the ASR-based version).
-/

-- Core
import SelfReference.Core.Interface
import SelfReference.Core.Representability
import SelfReference.Core.FixedPoint

-- Consequences
import SelfReference.Consequences.DiagonalBarrier

-- Instances
import SelfReference.Instances.NEMS
import SelfReference.Instances.Godel
import SelfReference.Instances.Kleene
import SelfReference.Instances.Loeb

-- Minimality
import SelfReference.Minimality.Countermodels
import SelfReference.Minimality.StratifiedReflection
