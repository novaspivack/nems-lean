# nems-lean: Overview for users

This document is for **outside parties** who want to use or build on the libraries (SelfReference, Closure, NemS) without reading the full papers first. It covers what each part is, how to import it, and how the pieces fit together.

---

## 1. General Self-Reference Calculus (SelfReference library)

### What it is

The **SelfReference** library formalizes a minimal interface for self-reference (the SRI: Self-Reference Interface) and proves two master theorems once:

- **MFP-1 (Master Fixed-Point Theorem):** For any transformer `F : Code → Obj`, there exists `p : Obj` such that `p ≃ F(quote p)`. This is the correct abstract form of Gödel’s diagonal lemma, Kleene’s recursion theorem, and the NEMS fixed-point construction.
- **MFP-2 (Master Diagonal Barrier):** In any such system (in the unityped setting), no extensional nontrivial predicate has a total decider within the representable class.

Gödel, Kleene, Löb, and NEMS are **instances**: they provide the SRI data (Obj, Code, quote, run, repr, axioms), and the master theorems then apply.

### Main types and names

- **`SelfReference.SRI' Obj Code`** — Two-sorted interface: `Equiv`, `quote`, `run`, `repr`, `repr_spec`, `eval_quote`.
- **`SelfReference.CSRI' Obj Code`** — SRI' plus congruence of quote/run (for the unityped corollary).
- **`SelfReference.SRI α`** / **`SelfReference.CSRI α`** — Unityped alias (Obj = Code = α).
- **MFP-1:** `SelfReference.CSRI'.master_fixed_point` (two-sorted), `SelfReference.CSRI.master_fixed_point` (unityped corollary).
- **MFP-2:** `SelfReference.Consequences.no_total_decider`, etc.
- **Instances:** `SelfReference.Instances.Godel`, `Kleene`, `Loeb`, `NEMS`.

### How to use it

- **Use the master theorems for your own system:** Define types `Obj` and `Code`, and an instance of `SRI' Obj Code` (or `CSRI' Obj Code`). Then import `SelfReference.Core.FixedPoint` and `SelfReference.Consequences.DiagonalBarrier`; MFP-1 and MFP-2 apply.
- **Or go through the Closure bridge:** If your setting is a “theory” with observational semantics and you have internal representability (see below), use `Closure.TheoryWithInternalRepr` and the bridge to get an `SRI'` instance automatically.

### Where in the repo

- Root barrel: **`SelfReference.lean`**
- Core: **`SelfReference/Core/Interface.lean`**, **Representability.lean**, **FixedPoint.lean**
- Consequences: **`SelfReference/Consequences/DiagonalBarrier.lean`**
- Instances: **`SelfReference/Instances/`** (Godel, Kleene, Loeb, NEMS)
- Minimality: **`SelfReference/Minimality/`** (countermodels, stratified trichotomy)

Module docstrings (in the `.lean` files) are the API-level reference.

---

## 2. Closure toolkit (Closure library)

### What it is

The **Closure** library is a physics-agnostic API for “theories about systems”: observational semantics, world-types (quotient by observational equivalence), selectors (sections of that quotient), and a parameterized notion of **internality**. It provides:

- **Audit soundness (factorization):** The core theorem is that any predicate decidable purely on world-types is observationally invariant (`audit_soundness`). So any decider for a non-invariant predicate cannot factor through the quotient—it must depend on a choice of representative. That is `not_invariant_implies_not_decidable_on_world_type`. Selector *existence* is stated separately as `selector_exists_classical` (uses Choice) and is not a consequence of non-invariance.
- **Internal outsourcing (U2):** When “internal” is instantiated (computable, definable) and the semantics has **effective presentation** or **canonicalization**, internal decider for a non-invariant P implies internal symmetry-breaking (internal selector). See `Closure.Core.Canonicalization` (canon induces selector; internal canon ⇒ internal selector under `InternalCanonImpliesInternalSelector`) and `Closure.Core.Effective` (EffectiveSemantics: enum + decidable ObsEquiv). **Nailed instance:** `Closure.Theorems.BoundedSelector` — given a **bounded cover** (every world-type has a representative in the first N enum positions) plus canonicalization, a selector exists (classical); with a **decidable membership test** for types (e.g. `DecidableEq WorldType`), bounded search yields a **total** selector (no Choice). Toy: `Closure.Examples.FintypeWorld` — when `[Fintype World]` and decidable ObsEquiv, effective semantics and a bounded cover are built, so a selector exists.
- **Bridge (repr only vs full):** `Closure.TheoryWithRepr` → `SelfReference.SRI0'` (MFP-1 from repr_spec only). `Closure.TheoryWithReprPlus` (adds `eval_quote`) → `SelfReference.SRI'` (full interface). So Gödel-style systems that don’t satisfy eval_quote still get the diagonal lemma via SRI0'.

So: Closure defines the objects/codes/fragments and what “internal” means; SelfReference supplies fixed points and barriers when internality implies repr.

### Main types and names

- **`Closure.ObsSemantics World Obs`** — `Holds : World → Obs → Prop`; induces `ObsEquiv`, `WorldType` (quotient), `toWorldType`, `Invariant`, `Categorical`, `NeedsSelection`.
- **`Closure.Selector S`** — Section of the quotient: `sel : S.WorldType → World`, `sec : toWorldType (sel t) = t`.
- **`Closure.InternalPred α`** — Typeclass with `Internal : α → Prop` (parameterized “internal”; you instantiate it).
- **`Closure.DecidableOnWorldType S P`** — P is decided by some map on world-types.
- **`Closure.audit_soundness`** — DecidableOnWorldType P ⇒ Invariant P (factorization; no Choice).
- **`Closure.not_invariant_implies_not_decidable_on_world_type`** — The sharp “no free bits” contrapositive.
- **`Closure.selector_exists_classical`** — Nonempty (Selector S) under Choice (separate from non-invariance).
- **`Closure.Canonicalization S`** — `canon : World → World` with canon w ~ w and (canon w₁ = canon w₂) ↔ w₁ ~ w₂; induces a selector. **`Closure.EffectiveSemantics`** — ObsSemantics + enum + decidable ObsEquiv. **`Closure.BoundedCover E`** — bound such that every world-type has a rep in enum 0..(cover-1). **`Closure.boundedSelectorAsSelector`** — total selector by bounded search (needs `DecidableEq WorldType`). **`Closure.Examples.FintypeWorld`** — toy: finite World ⇒ effective semantics + bounded cover ⇒ selector.
- **`Closure.TheoryWithRepr`** → **`SelfReference.SRI0'`**; **`Closure.TheoryWithReprPlus`** → **`SelfReference.SRI'`**.

### How to use it

- **Audit / invariance:** Define `ObsSemantics World Obs`, then prove that a predicate P is (or isn’t) `DecidableOnWorldType`; audit soundness gives invariance or its contrapositive.
- **Bridge to SelfReference:** If your theory has the repr data, pack it into `TheoryWithInternalRepr Obj Code`; then you get `[SRI' Obj Code]` and can use MFP-1 and MFP-2.

### Where in the repo

- Root barrel: **`Closure.lean`**
- Core: **`Closure/Core/ObsSemantics.lean`**, **Selector.lean**, **Internal.lean**, **Canonicalization.lean**, **Effective.lean**
- Theorems: **`Closure/Theorems/AuditSoundness.lean`**, **Preservation.lean**, **BoundedSelector.lean** (nailed instance)
- Bridge: **`Closure/Bridge/SelfReferenceInstance.lean`**
- Examples: **`Closure/Examples/FintypeWorld.lean`** (toy: finite worlds ⇒ selector)

---

## 3. How they fit together

- **SelfReference** is the “universal self-reference kernel”: minimal axioms (repr_spec, then eval_quote for the unityped corollary) and two master theorems. Any system that implements the interface gets the theorems.
- **Closure** is the “theory/audit” layer: observational semantics, selectors, internality, and audit soundness. When a theory in this sense has internal representability, the **A0 bridge** turns it into an SRI' instance, so SelfReference applies.
- **NemS** is the main application: NEMS framework, diagonal barrier (Theorem 5.9), PSC, etc. It uses both the concrete diagonal machinery and (where applicable) the SelfReference instances.

So for external use:

- **Only fixed points / barriers for a custom self-referential system:** Implement `SRI' Obj Code` (or use `TheoryWithInternalRepr` if you’re in a Closure-style theory) and import SelfReference.
- **Only audit / invariance for observational theories:** Use Closure (ObsSemantics, Selector, audit_soundness).
- **Both:** Use Closure for the theory side and the bridge to SelfReference for the diagonal consequences.

---

## 4. References

- **Paper 26:** *A General Self-Reference Calculus* — main reference for the SRI, MFP-1, MFP-2, and instances.
- **MANIFEST.md:** Verified theorem list, sorry count, and file-level layout.
- **GSRC_Significance** (in the suite): Short significance note for the General Self-Reference Calculus.
