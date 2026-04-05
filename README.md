# nems-lean

Lean 4 formalization of the **NEMS (No External Model Selection)** framework—the core logical spine of the NEMS/PSC suite and its machine-checked bridge to MFRR (Mathematical Foundations of Reflexive Reality).

## What This Repo Is

nems-lean formalizes the foundational theorems of the NEMS programme: the trichotomy of foundational theories, the diagonal barrier (no total effective adjudicator on diagonal-capable fragments), the closure/audit toolkit, and the bridge to transputation and MFRR. It covers Papers 26–51 of the NEMS suite, including SelfReference, Closure, Reflection, SelectorStrength, Learning, EpistemicAgency, InstitutionalEpistemics, CertificationLogic, SemanticSelfDescription, and physics-arc libraries (ArrowOfTime, BlackHoles, GPTClosure, LawCalibration, etc.).

## Build

**Requirements:** Lean 4.29.0-rc6, Mathlib v4.29.0-rc6

```bash
lake update
lake build
```

**Note:** Build from the repo root. Do not build individual libraries in isolation (e.g. `lake build CertificationLogic` alone)—cross-library resolution can fail.

## Documentation

| Document | Description |
|----------|-------------|
| [MANIFEST.md](MANIFEST.md) | Full artifact manifest, theorem catalog, sorry accounting, file list |
| [ARTIFACT.md](ARTIFACT.md) | What the artifact proves, proof status, fully verified theorems |
| [docs/](docs/) | Additional documentation |

## Related Repos

- **[ugp-lean](https://github.com/novaspivack/ugp-lean)** — Lean 4 formalization of the Universal Generative Principle (UGP) and Generative Triple Evolution (GTE). RSUC, sieve, orbit, Quarter-Lock, and gauge couplings. Certified in ugp-lean; bridges to Paper 25 (Unified Rigidity).
- **NEMS papers** — The LaTeX papers live in the Particle Derivations workspace (`Physics_Papers/NEMS_PAPERS/`). nems-lean is the mechanized spine referenced by those papers.

## License

See [LICENSE](LICENSE).
<!-- NOVA_ZPO_ZENODO_SOFTWARE_BEGIN -->
**Archival software (Zenodo):** https://doi.org/10.5281/zenodo.19429227
<!-- NOVA_ZPO_ZENODO_SOFTWARE_END -->
