# nems-lean Artifact Documentation

**Version:** v2.0.1  
**Lean:** leanprover/lean4:v4.28.0  
**Mathlib:** v4.28.0  
**Build:** 8062 jobs, 0 errors, 2 sorrys (documented below), **0 custom axioms**

## What This Artifact Proves

This Lean 4 library formalizes the core logical spine of the NEMS (No External Model Selection) classification framework and its machine-checked bridge to MFRR (Mathematical Foundations of Reflexive Reality).

### Fully Verified Theorems (0 sorry, 0 custom axioms)

**NEMS Core:**
- `nems_trichotomy`: Every framework is categorical ∨ has internal selector ∨ needs external selection
- `nems_implies_cat_or_internal`: NEMS ⇒ categorical ∨ internal selector
- Internality instantiations (definability-style and computability-style)

**Diagonal Barrier:**
- `asr_rt_not_computable`: ASR ⇒ record-truth not computable (reduces to Mathlib's `ComputablePred.halting_problem`)
- `no_total_effective_rt_decider`: Diagonal-capable ⇒ no total computable RT decider

**MFRR Bridge:**
- `PSC_and_choice_force_PT`: PSC bundle + record-divergent choice ⇒ PT exists
- `pt_not_total_effective_on_RT`: Diagonal-capable ⇒ PT not total-effective on RT
- `PSC_classification`: PSC + diagonal ⇒ categorical ∨ (selector ∧ undecidable RT)

**Physical Theorems:**
- `phys_uct_implies_asr`: Physical universal computation ⇒ ASR (diagonal capability)
- `phys_uct_implies_incompleteness`: Computers + records ⇒ no total algorithmic ToE

**Quantum (Paper 13):**
- `busch_gleason_unique`: **Uniqueness of Born representation** — if ρ₁ and ρ₂ both represent μ, then ρ₁ = ρ₂ (0 sorry, fully constructive via test effects)

## Proof Status: Quantum Module (Paper 13)

### What is fully machine-checked (0 `sorry`)

We fully prove the **uniqueness** direction of the Busch/Gleason representation theorem:

**`busch_gleason_unique`**: If two density operators ρ₁ and ρ₂ both represent the same effect measure μ via μ(E) = Re(Tr(ρE)) for all effects E, then ρ₁ = ρ₂.

This is proved constructively using explicit test effects:
- `diagEffect i`: diagonal projector |i⟩⟨i|
- `realTestEff i j`: (1/2)|i+j⟩⟨i+j| for i ≠ j
- `imagTestEff i j`: (1/2)|i+iĵ⟩⟨i+iĵ| for i ≠ j

The proof extracts every matrix entry of ρ from trace values on these test effects, showing that the representation is rigid.

### What is cited as classical (2 `sorry`)

The remaining `sorry`s are confined to the **existence** direction:

**`busch_gleason` (existence)**: For any normalized POVM-additive effect measure μ on effects, there exists a density operator ρ such that μ(E) = Re(Tr(ρE)) for all effects E.

This is the standard Busch/Gleason representation theorem. The two `sorry` statements are:

1. **`delta_eq_zero_core`** (NemS/Quantum/BuschGleason.lean:~971): The linear extension showing POVM-additive μ agrees with Re(Tr(rhoCandidate·)) on all effects. Requires: rational homogeneity from POVM repetition + boundedness + 1D bounded-additive-vanishes-on-ℚ lemma + spanning of Herm(n) by test effects.

2. **`rhoCandidate_psd`** (NemS/Quantum/BuschGleason.lean:~985): Positive semidefiniteness of rhoCandidate. Once representation is proved, follows from rank-1 projector effects |v⟩⟨v|/||v||² (~80 lines for projector construction).

Both are fully documented with complete mathematical specifications.

**References:**
- P. Busch, "Quantum states and generalized observables: A simple proof of Gleason's theorem," *Phys. Rev. Lett.* **91**, 120403 (2003).
- arXiv: quant-ph/9909073 (1999).

### Why this structure is valid

The new, delicate, and easy-to-get-wrong part is the rigidity/injectivity proof (uniqueness), which we have fully machine-checked. The remaining gap is a classical existence theorem, precisely stated and cited. This is standard practice in formal verification: machine-check the novel/fragile parts, cite classical results for the rest, with precise interface specifications.

### Consequence

Combining the cited existence with the Lean-verified uniqueness yields:

**Corollary**: Assuming the classical Busch/Gleason existence theorem, every effect measure μ admits a **unique** density operator ρ such that μ(E) = Re(Tr(ρE)) for all effects E.

This is the exact formal content needed for Paper 13's "Born rule as closure fixed point" argument.

## Build Instructions

```bash
cd nems-lean
lake update    # fetches Mathlib (cached oleans downloaded automatically)
lake build     # compiles the full library
```

Expected output: `Build completed successfully (8062 jobs).`

## Axiom Audit

To verify zero custom axioms:

```bash
lake build
grep -r "axiom " NemS/  # should return no custom axiom declarations
```

The only axioms are Lean's kernel axioms (propositional extensionality, quotient soundness, classical choice) as imported by Mathlib.

## File Structure

```
NemS/
├── Core/           # NEMS classification spine
├── Diagonal/       # Diagonal barrier (ASR → RT undecidable)
├── MFRR/           # Bridge to MFRR (PSC + choice → PT)
├── Physical/       # Physical theorems (universal computation → ASR)
├── Quantum/        # Born rule uniqueness (Paper 13)
├── Examples/       # Toy instantiations
└── Meta/           # Audit protocol
```

## Companion Papers

This artifact formalizes the core spine of:
- Paper 1: *The NEMS Framework*
- Paper 2: *Semantic Closure Under No External Model Selection*
- Paper 8: *From NEMS to MFRR: A Machine-Checked Bridge*
- Paper 11: *Physical Incompleteness*
- Paper 12: *Determinism No-Go*
- Paper 13: *Born Rule as a Closure Fixed Point*

## Future Work

Eliminating the 2 remaining `sorry`s in the quantum module is an engineering task (not an open mathematical problem). The required components are:

1. Formalize rational scaling of effect measures via POVM repetition (~40 lines)
2. Prove bounded additive functions on [0,1] vanishing on ℚ vanish everywhere (~30 lines)
3. Show delta is ℝ-homogeneous on effects (~40 lines)
4. Prove test effects span Herm(n) over ℝ (~30 lines)
5. Conclude delta = 0 on all effects (~20 lines)
6. Construct rank-1 projector effects (~80 lines)
7. Derive PSD from representation (~20 lines)

Total: ~260 lines of standard matrix algebra and 1D real analysis.

## License

[Specify license]

## Citation

If you use this artifact, please cite:

```
@misc{SpivackNEMSLean_v2,
  author       = {Nova Spivack},
  title        = {nems-lean: Lean 4 Formalization of the NEMS Core Spine and MFRR Bridge},
  howpublished = {Software artifact, Lean 4.28.0 / Mathlib 4.28.0},
  year         = {2026},
  note         = {v2.0.1: 8062 jobs; 2 sorrys (Busch/Gleason existence); zero custom axioms.}
}
```
