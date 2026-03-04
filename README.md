# nems-lean

Lean 4 formalization for the NEMS Suite: **NemS**, **SelfReference** (Paper 26), **Closure** (Paper 27), **Reflection** (Paper 28), **SelectorStrength** (Paper 29), **Learning** (Paper 30), **EpistemicAgency** (Paper 31), **SelfImprovement** (Paper 32), **SelfAwareness** (Paper 33), **Sieve** (Paper 34). **Paper 35** (Oracles) is a companion paper (Hypercomputation/ planned). **Paper 36** (Chronology Under Closure) — **ChronologyUnderClosure**. **Paper 37** (Black Hole Information) — **BlackHoles**.

**Lean 4** with **Mathlib v4.28.0**. Zero custom axioms; for current sorry count and verified theorems see [MANIFEST.md](MANIFEST.md).

## Libraries

| Library | Purpose |
|--------|---------|
| **NemS** | NEMS framework: world-types, selectors, diagonal barrier (Theorem 5.9), PSC bridge, audit protocol, and related results (Papers 1–25). |
| **SelfReference** | General Self-Reference Calculus (Paper 26): abstract SRI interface, MFP-1, MFP-2, and instances (Gödel, Kleene, Löb, NEMS). |
| **Closure** | Theory-closure and audit toolkit (Paper 27): observational semantics, world-types, selectors, internality, audit soundness, canonicalization, BoundedSelector, FintypeWorld, bridge to SelfReference. |
| **Reflection** | Reflection as a resource (Paper 28): SRI_R, DiagClosed, Diagonal Closure Theorem, hierarchy, bridge from Closure. |
| **SelectorStrength** | Selector strength and completion hierarchies (Paper 29): strength poset, barrier schema (no_total_decider_at_strength), monotonicity, bridges to Reflection/Closure, trivial and ComputableNat instances. |
| **Learning** | Second incompleteness for self-certifying learners (Paper 30): certificates, claims, no_total_self_certifier, reflection supplies hFP, stratified self-certification, ToyGuarantee. 0 sorry. |
| **EpistemicAgency** | Epistemic agency under diagonal constraints (Paper 31): society as verification protocol, strict separation (society > individual), diversity necessity, meta-barrier. 0 sorry. |
| **SelfImprovement** | Self-improvement under diagonal constraints (Paper 32): upgrade certificates, no total upgrade certifier, stratified improvement, protocol strict improvement, diversity necessity, meta-barrier. 0 sorry. |
| **SelfAwareness** | Self-awareness as a resource (Paper 33): claim hierarchy (C₀/C₁/C₂), no total certifier for C₂, selector necessity, introspective optimality barrier, ToyHierarchy, ToyRightness. 0 sorry. |
| **Sieve** | Sieve engine for theory spaces (Paper 34): TheorySpace, constraints as list, SieveHolds, Residual subtype, monotonicity (sieve_sublist, residual_mono), pullback/functoriality (sieve_pullback), ToyDomain. 0 sorry. |

For a short **user-oriented overview** of the libraries and how they connect, see **[docs/Overview.md](docs/Overview.md)**.

## Build

```bash
lake update
lake build
```

Expected: `Build completed successfully` (see MANIFEST.md for job count). See [MANIFEST.md](MANIFEST.md) for reproduction and checksums.

## Papers and manifest

- **Paper 26:** *A General Self-Reference Calculus* — `SelfReference` library.
- **Paper 27:** *A No-Free-Bits Calculus for Determinacy and Outsourcing* — `Closure` library.
- **Paper 28:** *Reflection as a Resource* — `Reflection` library.
- **Paper 29:** *Selector Strength and Completion Hierarchies* — `SelectorStrength` library.
- **Paper 30:** *Second Incompleteness for Self-Certifying Learners* — `Learning` library (0 sorry).
- **Paper 31:** *Epistemic Agency Under Diagonal Constraints* — `EpistemicAgency` library (0 sorry).
- **Paper 32:** *Self-Improvement Under Diagonal Constraints* — `SelfImprovement` library (0 sorry).
- **Paper 33:** *Self-Awareness as a Resource* — `SelfAwareness` library (0 sorry).
- **Paper 34:** *A Sieve Engine for Theory Spaces* — `Sieve` library (0 sorry).
- **Paper 35:** *Oracles as External Selectors* — companion paper (Lean library Hypercomputation/ planned).
- **Paper 36:** *Chronology Under Closure* — ChronologyUnderClosure library (0 sorry).
- **Paper 37:** *NEMS Constraints on Black Hole Information* — BlackHoles library (0 sorry).
- **MANIFEST.md:** Verified theorem list, sorry status, and library layout.
