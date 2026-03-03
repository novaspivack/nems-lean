# nems-lean

Lean 4 formalization for the NEMS/MFRR suite: **NemS**, **SelfReference** (Paper 26), **Closure** (Paper 27), and **Reflection** (Paper 28).

**Lean 4** with **Mathlib v4.28.0**. Zero custom axioms; for current sorry count and verified theorems see [MANIFEST.md](MANIFEST.md).

## Libraries

| Library | Purpose |
|--------|---------|
| **NemS** | NEMS framework: world-types, selectors, diagonal barrier (Theorem 5.9), PSC bridge, audit protocol, and related results (Papers 1–25). |
| **SelfReference** | General Self-Reference Calculus (Paper 26): abstract SRI interface, Master Fixed-Point Theorem (MFP-1), Master Diagonal Barrier (MFP-2), and instances (Gödel, Kleene, Löb, NEMS). Reusable for any system satisfying the interface. |
| **Closure** | Theory-closure and audit toolkit (Paper 27): observational semantics, world-types, selectors, internality, audit soundness, canonicalization, effective semantics, BoundedSelector, FintypeWorld, and the bridge from “internal representability” to SelfReference (A0/A1). |
| **Reflection** | Reflection as a resource (Paper 28): SRI_R, DiagClosed, Diagonal Closure Theorem, hierarchy, bridge from Closure. |

For a short **user-oriented overview** of the General Self-Reference Calculus and the Closure toolkit (what they are, how to use them, how they connect), see **[docs/Overview.md](docs/Overview.md)**.

## Build

```bash
lake update
lake build
```

Expected: `Build completed successfully` (8k+ jobs). See [MANIFEST.md](MANIFEST.md) for reproduction and checksums.

## Papers and manifest

- **Paper 26:** *A General Self-Reference Calculus* — corresponds to the `SelfReference` library and the significance note in the suite.
- **Paper 27:** *A No-Free-Bits Calculus for Determinacy and Outsourcing* — corresponds to the `Closure` library (audits, canonicalization, effective semantics, BoundedSelector, FintypeWorld).
- **Paper 28:** *Reflection as a Resource* — corresponds to the `Reflection` library (SRI_R, DiagClosed, Diagonal Closure Theorem, hierarchy, bridge from Closure).
- **MANIFEST.md:** Verified theorem list, sorry status, and library layout.
