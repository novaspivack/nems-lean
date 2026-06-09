# nems-lean


## Research Program

This repository is part of the **Reflexive Reality** research program by [Nova Spivack](https://www.novaspivack.com/).

**What this formalizes:** Papers 00–92 of the NEMS suite (self-reference, closure, reflection, selector strength, learning, epistemic agency, institutional epistemics, certification logic, semantic self-description, physics arc).

| Link | Description |
|------|-------------|
| [Research page](https://www.novaspivack.com/research/) | Full index of all papers, programs, and Lean archives |
| [Full abstracts](https://novaspivack.github.io/research/abstracts/#abs-b1-nems) | Complete abstract for this library's papers |
| [Zenodo program hub](https://doi.org/10.5281/zenodo.19429270) | Citable DOI hub for the NEMS program |

All results are machine-checked in Lean 4 with a zero-sorry policy on proof targets.
See [MANIFEST.md](MANIFEST.md) for the sorry audit (if present).

---

Lean 4 formalization of the **NEMS (No External Model Selection)** framework — the core logical spine of the NEMS suite and its machine-checked bridge to reflexive reality.

## What This Repo Is

nems-lean formalizes the foundational theorems of the NEMS programme: the trichotomy of foundational theories, the diagonal barrier (no total effective adjudicator on diagonal-capable fragments), the closure/audit toolkit, and the bridge to transputation. It covers the full NEMS suite (Papers 00–92), including SelfReference, Closure, Reflection, SelectorStrength, Learning, EpistemicAgency, InstitutionalEpistemics, CertificationLogic, SemanticSelfDescription, and physics-arc libraries (ArrowOfTime, BlackHoles, GPTClosure, LawCalibration, etc.).

### Diagonal classification theorems

The `NemS/Diagonal/` library sharpens the diagonal barrier from a non-computability lower bound to an exact degree classification of record-truth (all zero sorry, zero custom axioms):

- **`rt_sigma1_complete_on_diagonal`** (`NemS/Diagonal/Sigma1Completeness.lean`) — under an Arithmetic Self-Reference structure (ASR) and the finite-witness premise `Sigma1RecordTruth` (record-truth is Σ₁⁰: a computable witness flag certifies truth at a finite stage), record-truth `RT` is **many-one equivalent to the halting predicate**. Hardness (`halting_manyOne_reducible_to_RT`) is the certified `halts_iff_RT` + `encode_computable` bridge read as a many-one reduction; membership (`rt_manyOne_reducible_to_halting_zero`) goes through a computable witness search and code currying. Hence `RT` is Σ₁⁰-complete: Turing degree exactly **0′** — not merely undecidable, and not beyond the first jump.
- **`no_computable_convergence_modulus`** (`NemS/Diagonal/NoConvergenceModulus.lean`) — no total computable stage approximation of record-truth admits a total computable convergence modulus: such a modulus would make `RT` computably decidable, contradicting `asr_rt_not_computable`. Operationally: limit-stage answers exist, but no internal procedure can certify *when* the limit has been reached.
- **`NemS/Diagonal/Premises.lean`** — the premises enter as named structures (`Sigma1RecordTruth`, `RecordReadout`), never as bare axioms; `Sigma1RecordTruth.rePred` packages the Σ₁ membership as Mathlib's `REPred`.

These results feed the transputation classification in the companion repo [transputation-lean](https://github.com/novaspivack/transputation-lean): the internal adjudicator's decision content on the diagonal fragment sits at the halting degree — above total computation, strictly below hypercomputation.

## Build

**Requirements:** Lean 4.29.0-rc6, Mathlib v4.29.1

```bash
lake update
lake exe cache get   # download pre-built Mathlib .olean files (strongly recommended)
lake build
```

**Note:** Build from the repo root. Do not build individual libraries in isolation — cross-library resolution can fail.

## Documentation

| Document | Description |
|----------|-------------|
| [MANIFEST.md](MANIFEST.md) | Full artifact manifest, theorem catalog, sorry accounting, file list |
| [ARTIFACT.md](ARTIFACT.md) | What the artifact proves, proof status, fully verified theorems |
| [docs/](docs/) | Additional documentation |

## Related Repos

- **[ugp-lean](https://github.com/novaspivack/ugp-lean)** — Lean 4 formalization of the Universal Generative Principle (UGP). Bridges to Paper 25 (Unified Rigidity).
- **NEMS papers** — The companion papers (Papers 00–92 of the NEMS Suite) are published on Zenodo. See [novaspivack.com/research](https://www.novaspivack.com/research) for the full index.

## License

See [LICENSE](LICENSE).
<!-- NOVA_ZPO_ZENODO_SOFTWARE_BEGIN -->
**Archival software (Zenodo):** https://doi.org/10.5281/zenodo.19429227
<!-- NOVA_ZPO_ZENODO_SOFTWARE_END -->
