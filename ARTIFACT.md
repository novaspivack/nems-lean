# nems-lean Artifact Documentation

**Version:** v2.7.0  
**Lean:** leanprover/lean4:v4.29.0-rc3  
**Mathlib:** v4.29.0-rc3  
**Build:** 1713 jobs, 0 errors, 9 sorrys (6 in NemS/SelfReference, 3 in GPTClosure/Instances/QuantumFinite; see MANIFEST.md), **0 custom axioms**

**Lean 4.29 compatibility:** See `LEAN_4.29_UPGRADE_DISCLOSURE.md` for tactic/API fixes in BuschGleason.lean (no theorem changes).

## What This Artifact Proves

This Lean 4 library formalizes the core logical spine of the NEMS (No External Model Selection) framework and its machine-checked bridge to MFRR, plus the **abstract-core sequence (Papers 26–34)** and **physics-arc papers (36–40)**: SelfReference (26), Closure (27), Reflection (28), SelectorStrength (29), Learning (30), EpistemicAgency (31), SelfImprovement (32), SelfAwareness (33), Sieve (34). **Paper 35** (Oracles) is a companion paper (Hypercomputation/ planned). **Paper 36** (The Arrow of Time from Closure) — ArrowOfTime library (0 sorry). **Paper 37** (Chronology Under Closure) — ChronologyUnderClosure library (0 sorry). **Paper 38** (Black Hole Information) — BlackHoles library (0 sorry). **Paper 39** (Probability as Closure in GPTs) — GPTClosure library (0 sorry in core); GPTClosure/Instances/QuantumFinite bridges Paper 13 (quantum) ↔ Paper 39 (GPT), showing quantum probability is an instance of closure-forced probability (3 sorry: PSD cone pointedness, Born-rule nonnegativity, wiring to busch_gleason_unique). **Paper 40** (Institutions Under Diagonal Constraints) — InstitutionalEpistemics library (0 sorry). **Paper 41** (Refinement Flow of World-Types) — RefinementFlow library (0 sorry). **Paper 42** (Record Entropy and Noncomputability) — RecordEntropy library (0 sorry): recordEntropy, monotonicity, strict monotonicity, no_total_decider_entropy, ToyEntropy. **Paper 43** (Adjudication as Decoding) — ErrorCorrectingClosure library (0 sorry). **Paper 44** (Calibration as Closure) — LawCalibration library (0 sorry): lawSelectorClaim, no_total_decider_law_selector, fixed_point_multiplicity, ToyLaw. **Paper 45** (Local Dynamics, Global Semantics: Semantic Nonlocality) — SemanticNonlocality library (0 sorry): LocalityAxioms, same_local_views_imp_obs_equiv, same_local_views_imp_same_world_type, ToyFactorization. **Paper 46** (Causal Nonlocality from Closure) — CausalNonlocality library (0 sorry, 0 axioms): no_local_semantic_determinacy, toy_no_go (parametric in hFP; barrier witness by instantiation). **Paper 47** (No Spooky to Signal Compiler) — FTLConstraints (0 sorry). **Paper 48** (Holography Under Closure) — HolographyUnderClosure (0 sorry). **Paper 49** (Cosmic Audit) — InstitutionalEpistemics.CosmicAudit (1 sorry in ToyCosmic). **Paper 50** (Completeness of Stratified Certification Logics) — CertificationLogic (0 sorry): soundness_capstone, completeness_capstone, boundary_maximality, protocolCoverage_subset_union_atoms, toy_equiv, toy_boundary. For the full theorem table, sorry accounting, and file list see **[MANIFEST.md](MANIFEST.md)**.

### Abstract-core spine (Papers 26–34, 0 sorry in Learning, EpistemicAgency, SelfImprovement, SelfAwareness, Sieve)

- **Paper 26 (SelfReference):** MFP-1, MFP-2, instances (Gödel, Kleene, Löb, NEMS). Documented sorrys only in instance layers (NEMS fixed-point step, Löb HBL chaining).
- **Paper 27 (Closure):** Audit soundness, canonicalization, BoundedSelector, FintypeWorld, bridge to SelfReference.
- **Paper 28 (Reflection):** SRI_R, DiagClosed, restricted_master_fixed_point, method-level separation (identity-only not diagonally closed).
- **Paper 29 (SelectorStrength):** Barrier schema (no_total_decider_at_strength), monotonicity, reflection_supplies_hFP, trivial and ComputableNat instances.
- **Paper 30 (Learning):** no_total_self_certifier, reflection_supplies_hFP_for_learning, stratified_self_certification_toy, ToyGuarantee. **0 sorry.**
- **Paper 31 (EpistemicAgency):** Society as verification protocol, strict separation (society > individual), diversity necessity, meta-barrier. **0 sorry.**
- **Paper 32 (SelfImprovement):** Upgrade certificates, no_total_upgrade_certifier, stratified improvement, protocol strict improvement, diversity necessity, meta-barrier. **0 sorry.**
- **Paper 33 (SelfAwareness):** Claim hierarchy (C₀/C₁/C₂), no_total_certifier_C2, selector necessity, introspective optimality barrier, ToyHierarchy, ToyRightness. **0 sorry.**
- **Paper 34 (Sieve):** Theory space, constraints as list, SieveHolds, Residual subtype, sieve_sublist, residual_mono, pullbackConstraints, sieve_pullback (functoriality), ToyDomain. **0 sorry.**

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

**Reverse Direction (Paper 14):**
- `bics_implies_nems`: **BICS ⇒ NEMS** — Born as internal complete semantics implies no external model selection (0 sorry, fully proved)
- `bics_rules_out_external`: BICS ⇒ ¬ NeedsExternalSelection (0 sorry)

**GPT-Quantum Bridge (Paper 39 ↔ Paper 13):**
- `quantumCone`, `quantumOUS`: PSD cone defines an ordered unit space (1 sorry: pointedness)
- `born_rule_is_gpt_prob`: **Born rule equals GPT state-effect pairing** (1 sorry: nonnegativity for PSD operators)
- `povmToMeasurement`: POVMs map to GPT measurements (0 sorry)
- `quantum_state_uniqueness`: State uniqueness via GPT uniqueness theorem (1 sorry: wiring to busch_gleason_unique)

## Proof Status: Quantum Module (Paper 13)

### What is fully machine-checked (0 `sorry`)

We fully prove the **uniqueness** direction of the Busch/Gleason representation theorem:

**`busch_gleason_unique`**: If two density operators ρ₁ and ρ₂ both represent the same effect measure μ via μ(E) = Re(Tr(ρE)) for all effects E, then ρ₁ = ρ₂.

This is proved constructively using explicit test effects:
- `diagEffect i`: diagonal projector |i⟩⟨i|
- `realTestEff i j`: (1/2)|i+j⟩⟨i+j| for i ≠ j
- `imagTestEff i j`: (1/2)|i+iĵ⟩⟨i+iĵ| for i ≠ j

The proof extracts every matrix entry of ρ from trace values on these test effects, showing that the representation is rigid.

### What is cited as classical (4 `sorry` total, 2 distinct facts)

The remaining `sorry`s are confined to two standard mathematical facts:

#### Quantum module (Paper 13): Busch/Gleason existence

**`busch_gleason` (existence)**: For any normalized POVM-additive effect measure μ on effects, there exists a density operator ρ such that μ(E) = Re(Tr(ρE)) for all effects E.

This is the standard Busch/Gleason representation theorem. The two `sorry` statements are:

1. **`delta_eq_zero_core`** (NemS/Quantum/BuschGleason.lean:~971): The linear extension showing POVM-additive μ agrees with Re(Tr(rhoCandidate·)) on all effects. Requires: rational homogeneity from POVM repetition + boundedness + 1D bounded-additive-vanishes-on-ℚ lemma + spanning of Herm(n) by test effects.

2. **`rhoCandidate_psd`** (NemS/Quantum/BuschGleason.lean:~985): Positive semidefiniteness of rhoCandidate. Once representation is proved, follows from rank-1 projector effects |v⟩⟨v|/||v||² (~80 lines for projector construction).

Both are fully documented with complete mathematical specifications.

**References:**
- P. Busch, "Quantum states and generalized observables: A simple proof of Gleason's theorem," *Phys. Rev. Lett.* **91**, 120403 (2003).
- arXiv: quant-ph/9909073 (1999).

#### Reverse direction module (Paper 14): PSD trace nonnegativity

**`bics_prob_bounded`**: For PSD density operator ρ and effect E, Re(Tr(ρE)) ∈ [0,1].

This requires the standard fact that for PSD Hermitian matrices A, B over ℂ, Re(Tr(AB)) ≥ 0.
The two `sorry` statements (both instances of this fact) are:

1. **Re(Tr(ρE)) ≥ 0** (NemS/ReverseBICS/BICS.lean:~66): Nonnegativity of trace for PSD matrices.
2. **Re(Tr(ρ(I-E))) ≥ 0** (NemS/ReverseBICS/BICS.lean:~78): Same fact applied to I-E.

Both are standard results in finite-dimensional linear algebra. The proof uses spectral decomposition
or direct Frobenius inner product arguments.

**Reference:**
- Horn & Johnson, *Matrix Analysis* (standard finite-dimensional linear algebra).

### Why this structure is valid

The new, delicate, and easy-to-get-wrong part is the rigidity/injectivity proof (uniqueness), which we have fully machine-checked. The remaining gap is a classical existence theorem, precisely stated and cited. This is standard practice in formal verification: machine-check the novel/fragile parts, cite classical results for the rest, with precise interface specifications.

### Consequences

**For Paper 13 (forward direction):**
Combining the cited Busch/Gleason existence with the Lean-verified uniqueness yields:
every effect measure μ admits a **unique** density operator ρ such that μ(E) = Re(Tr(ρE)) for all effects E.

**For Paper 14 (reverse direction):**
The flagship theorem `bics_implies_nems` is **fully proved (0 sorry)**. The 2 sorrys in `bics_prob_bounded`
are auxiliary boundedness facts that don't affect the core BICS ⇒ NEMS implication.

**Fixed-point architecture:**
Forward (PSC ⇒ Born) + Reverse (BICS ⇒ NEMS ⇒ PSC) establishes PSC ↔ BICS equivalence within explicit scope.

## Build Instructions

```bash
cd nems-lean
lake update    # fetches Mathlib (cached oleans downloaded automatically)
lake build     # compiles the full library
```

Expected output: `Build completed successfully (1713 jobs).`

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
GPTClosure/
├── Core/           # Ordered spaces, effects/states, measurements
├── Theorems/       # Uniqueness, closure principles
├── Examples/       # Classical simplex toy
└── Instances/      # QuantumFinite (Paper 13 ↔ Paper 39 bridge)
```

## Companion Papers

This artifact formalizes the core spine of:
- Papers 1–2, 8, 11–14: NEMS framework, MFRR bridge, physical incompleteness, determinism no-go, Born rule, BICS ⇒ NEMS.
- **Paper 26:** *A General Self-Reference Calculus* (SelfReference)
- **Paper 27:** *A No-Free-Bits Calculus for Determinacy and Outsourcing* (Closure)
- **Paper 28:** *Reflection as a Resource* (Reflection)
- **Paper 29:** *Selector Strength and Completion Hierarchies* (SelectorStrength)
- **Paper 30:** *Second Incompleteness for Self-Certifying Learners* (Learning; 0 sorry)
- **Paper 31:** *Epistemic Agency Under Diagonal Constraints* (EpistemicAgency; 0 sorry)
- **Paper 32:** *Self-Improvement Under Diagonal Constraints* (SelfImprovement; 0 sorry)
- **Paper 33:** *Self-Awareness as a Resource* (SelfAwareness; 0 sorry)
- **Paper 34:** *A Sieve Engine for Theory Spaces* (Sieve; 0 sorry)
- **Paper 35:** *Oracles as External Selectors* (companion; Lean library Hypercomputation/ planned)
- **Paper 36:** *The Arrow of Time from Closure* (ArrowOfTime; 0 sorry)
- **Paper 37:** *Chronology Under Closure* (ChronologyUnderClosure; 0 sorry)
- **Paper 38:** *NEMS Constraints on Black Hole Information* (BlackHoles; 0 sorry)
- **Paper 39:** *Probability as Closure in GPTs* (GPTClosure; 0 sorry in core; GPTClosure/Instances/QuantumFinite bridges Paper 13 ↔ 39; 3 sorry)
- **Paper 40:** *Institutions Under Diagonal Constraints* (InstitutionalEpistemics; 0 sorry)
- **Paper 50:** *A Complete Logic of Certification: Soundness, Completeness, and Maximality for Stratified Verification Protocols* (CertificationLogic; 0 sorry): soundness_capstone, completeness_capstone, boundary_maximality, protocolCoverage_subset_union_atoms, toy_equiv, toy_boundary. Build: full `lake build` (see NEMS_LEAN_BUILD_NOTE.md).

## Future Work

Eliminating the remaining `sorry`s in the quantum module and QuantumFinite bridge is an engineering task (not an open mathematical problem).

### Quantum module (Paper 13): 2 sorrys

The required components are:

1. Formalize rational scaling of effect measures via POVM repetition (~40 lines)
2. Prove bounded additive functions on [0,1] vanishing on ℚ vanish everywhere (~30 lines)
3. Show delta is ℝ-homogeneous on effects (~40 lines)
4. Prove test effects span Herm(n) over ℝ (~30 lines)
5. Conclude delta = 0 on all effects (~20 lines)
6. Construct rank-1 projector effects (~80 lines)
7. Derive PSD from representation (~20 lines)

Total: ~260 lines of standard matrix algebra and 1D real analysis.

### QuantumFinite bridge (Paper 39 ↔ Paper 13): 3 sorrys

1. PSD cone pointedness: spectral argument that H and −H both PSD ⇒ H = 0 (~20 lines)
2. Born-rule nonnegativity: Re(Tr(ρE)) ≥ 0 for PSD ρ, E (~15 lines, standard Frobenius inner product)
3. Wiring to busch_gleason_unique: unpack densityToState/quantumEffectToGPT to show agreement on all effects implies agreement on test effects, then apply busch_gleason_unique (~40 lines)

Total: ~75 lines of standard linear algebra.

## License

[Specify license]

## Citation

If you use this artifact, please cite:

```
@misc{SpivackNEMSLean_v2,
  author       = {Nova Spivack},
  title        = {nems-lean: Lean 4 Formalization of the NEMS Core Spine and MFRR Bridge},
  howpublished = {Software artifact, Lean 4.29.0-rc3 / Mathlib 4.29.0-rc3},
  year         = {2026},
  note         = {v2.5.0+: 8k+ jobs; 6 sorrys (see MANIFEST); Papers 26–31 abstract-core spine including EpistemicAgency; zero custom axioms.}
}
```
