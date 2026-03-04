# nems-lean: Overview for users

This document is for **outside parties** who want to use or build on the libraries (SelfReference, Closure, Reflection, SelectorStrength, Learning, EpistemicAgency, SelfImprovement, SelfAwareness, Sieve, NemS) without reading the full papers first. It covers what each part is, how to import it, and how the pieces fit together.

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
- **Reflection** (Paper 28) adds stratified representability (SRI_R, DiagClosed); **SelectorStrength** (29) the barrier hierarchy; **Learning** (30) the self-certifier barrier; **EpistemicAgency** (31) society as verification protocol; **SelfImprovement** (32) upgrade-certifier barrier and society-improves-improvement; **SelfAwareness** (33) limits of self-awareness (hierarchy, selector necessity, rightness barrier); **Sieve** (34) meta-methodology kernel for theory spaces (constraints as list, residual subtype, monotonicity, pullback/functoriality). **Paper 35** (Oracles as External Selectors) applies Closure and SelectorStrength to hypercomputation; its Lean library (Hypercomputation/) is planned. **Paper 36** (Chronology Under Closure) applies the same framework to time travel (record dynamics, selection barrier); **Paper 37** (Black Hole Information) to record consistency and no-hypercomputing-from-BH; both have Lean libraries (ChronologyUnderClosure, BlackHoles; 0 sorry).
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

## 6. EpistemicAgency (Paper 31)

### What it is

The **EpistemicAgency** library turns the Papers 26–30 spine into a theorem-grade theory of **epistemic agency and social verification**. It formalizes society as a verification protocol (finite verifiers, soundness-on-coverage, admissible aggregation), proves **strict separation** (some society+protocol has certified coverage strictly larger than any individual), and **diversity necessity** (homogeneous societies cannot strictly improve; role diversity is necessary). A **meta-barrier** shows that society+protocol as a single diagonal-capable system cannot totally self-certify (Paper 30 barrier reappears at the societal level).

### Where in the repo

- Root barrel: **`EpistemicAgency.lean`**
- Core: **`EpistemicAgency/Core/ClaimDomain.lean`**, **Agent.lean**, **Protocol.lean**
- Theorems: **NoSelfCertifierImported.lean**, **ProtocolStrictImprovement.lean**, **Diversity.lean**, **MetaBarrier.lean**
- Examples: **`EpistemicAgency/Examples/ToySociety.lean`**

---

## 7. SelfImprovement (Paper 32)

### What it is

The **SelfImprovement** library applies the barrier spine to **self-improvement**: upgrade certificates, good-predicates, and internal certifiers. It proves **no total internal self-upgrade certifier** under diagonal capability (Paper 30 applied to Cert = Agent × Upgrade), **stratified improvement** (positive result when hFP is not supplied), **protocol strict improvement** and **diversity necessity** for upgrade verification (via EpistemicAgency), and a **meta-barrier** for self-improvement at the societal level.

### Where in the repo

- Root barrel: **`SelfImprovement.lean`**
- Core: **`SelfImprovement/Core/Upgrades.lean`**
- Theorems: **Barrier.lean**, **Stratified.lean**, **SocietyImproves.lean**, **MetaBarrier.lean**
- Examples: **`SelfImprovement/Examples/ToyUpgrades.lean`**

---

## 8. SelfAwareness (Paper 33)

### What it is

The **SelfAwareness** library formalizes **limits of self-awareness** as internal certification capacity over claim classes. It proves: (i) **hierarchy** — base class C₀ can have a total certifier (witness: ToyHierarchy), class C₂ has no total certifier under diagonal capability (Paper 30 barrier); (ii) **selector necessity** — when multiple observationally indistinguishable self-model fixed points exist, selection cannot be total-effective internally (SelectorNecessity + Learning barrier); (iii) **introspective optimality barrier** — no total internal rightness certifier under diagonal capability, with stratified positive examples (ToyRightness). ToyMultiplicity gives two indistinguishable fixed points (Fin 2, identity update).

### Where in the repo

- Root barrel: **`SelfAwareness.lean`**
- Core: **`SelfAwareness/Core/ClaimFamilies.lean`**, **SelfModel.lean**
- Theorems: **Hierarchy.lean**, **SelectorNecessity.lean**, **IntrospectiveOptimality.lean**
- Examples: **ToyHierarchy.lean**, **ToyMultiplicity.lean**, **ToyRightness.lean**

---

## 9. Sieve (Paper 34)

### What it is

The **Sieve** library is a **meta-methodology kernel** for theory spaces: a type of candidates α, optional equivalence and canonicalization (same structure as Closure’s canonicalization), constraints as a list of predicates (α → Prop), a sieve as the conjunction (List.Forall), and a residual as the subtype { a : α // SieveHolds cs a }. It proves **monotonicity** (adding constraints shrinks the residual; sieve_sublist, residual_mono) and **residual functoriality** (pullback of constraints along a map f : α → β preserves sieve membership; pullbackConstraints, sieve_pullback). Proof-carrying enumeration: external generators propose candidates plus certificates; Lean verifies. ToyDomain illustrates with Fin 3 and two constraints.

### Main types and names

- **`Sieve.TheorySpace α`** — Type of candidates with optional Equiv and canon.
- **`Sieve.Constraint α`** — α → Prop.
- **`Sieve.SieveHolds cs a`** — Candidate a satisfies every constraint in list cs.
- **`Sieve.Residual cs`** — Subtype { a // SieveHolds cs a }.
- **`Sieve.sieve_sublist`**, **`Sieve.residual_mono`** — Monotonicity (cs.Sublist cs' ⇒ smaller residual).
- **`Sieve.pullbackConstraints f ds`** — Pullback of constraint list on β to α along f.
- **`Sieve.sieve_pullback`** — SieveHolds (pullback f ds) a ↔ SieveHolds ds (f a).
- **`Sieve.Examples.ToyDomain`** — toySpace (Fin 3), toySieve, toy_residual_nonempty.

### Where in the repo

- Root barrel: **`Sieve.lean`**
- Core: **`Sieve/Core/TheorySpace.lean`**, **Constraints.lean**
- Theorems: **`Sieve/Theorems/Residual.lean`**
- Examples: **`Sieve/Examples/ToyDomain.lean`**

---

## 10. References

- **Paper 26:** *A General Self-Reference Calculus* — SRI, MFP-1, MFP-2, and instances.
- **Paper 27:** *A No-Free-Bits Calculus* — Closure library, audit soundness, BoundedSelector.
- **Paper 28:** *Reflection as a Resource* — SRI_R, DiagClosed, restricted_master_fixed_point.
- **Paper 29:** *Selector Strength and Completion Hierarchies* — barrier schema, strength poset, bridges.
- **Paper 30:** *Second Incompleteness for Self-Certifying Learners* — no total self-certifier, stratified self-certification, Learning library.
- **Paper 31:** *Epistemic Agency Under Diagonal Constraints* — society as verification protocol, strict separation, diversity necessity, EpistemicAgency library.
- **Paper 32:** *Self-Improvement Under Diagonal Constraints* — no total upgrade certifier, stratified improvement, society improves improvement, SelfImprovement library.
- **Paper 33:** *Self-Awareness as a Resource* — hierarchy, selector necessity, introspective optimality barrier, SelfAwareness library.
- **Paper 34:** *A Sieve Engine for Theory Spaces* — theory space, constraints as list, SieveHolds, Residual, monotonicity, pullback/functoriality, Sieve library.
- **Paper 35:** *Oracles as External Selectors* — oracle-as-selector (Closure), no internal hypercomputer (SelectorStrength), hypercomputation taxonomy; Lean library Hypercomputation/ planned.
- **Paper 36:** *Chronology Under Closure* — record dynamics, self-consistent loops, record_non_overwrite, selection_barrier_chronology; ChronologyUnderClosure library (0 sorry).
- **Paper 37:** *NEMS Constraints on Black Hole Information* — record fragments, record_consistency_abstract, no_hypercomputing_from_bh; BlackHoles library (0 sorry).
- **MANIFEST.md:** Verified theorem list, sorry count, and file-level layout.
- **GSRC_Significance** (in the suite): Short significance note for the General Self-Reference Calculus.
