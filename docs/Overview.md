# nems-lean: Overview for users

This document is for **outside parties** who want to use or build on the libraries (SelfReference, Closure, Reflection, SelectorStrength, Learning, NemS) without reading the full papers first. It covers what each part is, how to import it, and how the pieces fit together.

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

## 4. Selector Strength (SelectorStrength library, Paper 29)

### What it is

The **SelectorStrength** library formalizes a **poset of realizability strengths** (deciders/transformers) and the **barrier theorem family**: under anti-decider closure and a fixed-point principle at a strength level, no total decider exists in that strength for nontrivial extensional predicates. Reflection supplies the fixed-point premise when R is diagonally closed; Closure supplies the selector-at-strength vocabulary.

### Main types and names

- **`SelectorStrength.Core.Strength`** — Strength as `(α → β) → Prop`; `Strength.le` (preorder).
- **`SelectorStrength.Core.Deciders`** — `TotalDecider`, `DecidableAt`, `Extensional`, `Nontrivial`.
- **`SelectorStrength.Core.AntiDecider`** — `antiDecider`, `AntiDeciderClosed`.
- **`SelectorStrength.Theorems.BarrierSchema.no_total_decider_at_strength`** — Headline: hExt, hNontriv, AntiDeciderClosed, hFP ⇒ ¬ DecidableAt Sbool T.
- **`SelectorStrength.Bridge.Reflection.reflection_supplies_hFP`** — DiagClosed R ⇒ fixed-point premise.
- **`SelectorStrength.Bridge.Closure.SelectorAt`** — Selector whose section is in a given strength class.
- **Instances:** `SelectorStrength.Instances.Trivial` (S_all; barrier corollary), `SelectorStrength.Instances.ComputableNat` (parametric barrier on Nat).

### Where in the repo

- Root barrel: **`SelectorStrength.lean`**
- Core: **`SelectorStrength/Core/Strength.lean`**, **Deciders.lean**, **AntiDecider.lean**
- Theorems: **`SelectorStrength/Theorems/BarrierSchema.lean`**, **Monotonicity.lean**
- Bridges: **`SelectorStrength/Bridge/Reflection.lean`**, **Closure.lean**
- Instances: **`SelectorStrength/Instances/Trivial.lean`**, **ComputableNat.lean**

---

## 5. Learning (Learning library, Paper 30)

### What it is

The **Learning** library applies the SelectorStrength barrier to **self-trust in learning systems**: certificates, claims (guarantee predicates), and internal verifiers. It proves that **no total internal self-certifier** exists for any nontrivial extensional claim when the strength is anti-decider closed and has the fixed-point premise (hFP). Reflection supplies hFP when the representability class R is diagonally closed. A **positive result** (stratified self-certification): when hFP is not supplied (e.g. R not diagonally closed), total verifiers can exist for some claims; the toy claim (n=0 on ℕ) has a total decider at S_all when hFP is not assumed.

### Main types and names

- **`Learning.Core.Certificates`** — Claim, TotalDecider, Extensional, Nontrivial (re-exports Deciders).
- **`Learning.Core.SelfTrust`** — SelfCertifierAtStrength, selfCertifierAtStrength_iff.
- **`Learning.Theorems.SelfTrustBarrier.no_total_self_certifier`** — Headline: Extensional + Nontrivial + AntiDeciderClosed + hFP ⇒ ¬ DecidableAt Sbool Claim.
- **`Learning.Bridge.Reflection`** — reflection_supplies_hFP_for_learning, barrier_premise_from_reflection.
- **`Learning.Examples.ToyGuarantee`** — ToyClaim (n=0), toyClaim_extensional, toyClaim_nontrivial, no_total_self_certifier_toy.
- **`Learning.Positive.Stratified.stratified_self_certification_toy`** — DecidableAt S_all ToyClaim (positive result when hFP not assumed).

### Where in the repo

- Root barrel: **`Learning.lean`**
- Core: **`Learning/Core/Certificates.lean`**, **SelfTrust.lean**
- Theorems: **`Learning/Theorems/SelfTrustBarrier.lean`**
- Bridge: **`Learning/Bridge/Reflection.lean`**
- Examples: **`Learning/Examples/ToyGuarantee.lean`**
- Positive: **`Learning/Positive/Stratified.lean`**

---

## 6. References

- **Paper 26:** *A General Self-Reference Calculus* — SRI, MFP-1, MFP-2, and instances.
- **Paper 28:** *Reflection as a Resource* — SRI_R, DiagClosed, restricted_master_fixed_point.
- **Paper 29:** *Selector Strength and Completion Hierarchies* — barrier schema, strength poset, bridges.
- **Paper 30:** *Second Incompleteness for Self-Certifying Learners* — no total self-certifier, stratified self-certification, Learning library.
- **MANIFEST.md:** Verified theorem list, sorry count, and file-level layout.
- **GSRC_Significance** (in the suite): Short significance note for the General Self-Reference Calculus.
