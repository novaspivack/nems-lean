# nems-lean — Artifact Manifest

**Release:** v2.7.0  
**Date:** March 2026  
**Lean version:** leanprover/lean4:v4.29.0-rc6  
**Mathlib version:** v4.29.0-rc6  
**Build result:** Current clean build succeeds with the pinned toolchain. See the reproduction section for the exact current build outcome, and see the theorem tables below for current theorem coverage and sorry-status.

**Lean 4.29 upgrade:** Compatibility fixes in `BuschGleason.lean` (tactic/API only; no theorem changes). See `LEAN_4.29_UPGRADE_DISCLOSURE.md`.

## v2.2.0 additions: General Self-Reference Calculus

A new `SelfReference` library has been added alongside `NemS`.  It extracts
the NEMS diagonal machinery into an abstract interface (the SRI) and proves
a master fixed-point theorem (MFP-1) and master diagonal barrier (MFP-2)
once, recovering Gödel, Kleene, Löb, and NEMS as instances.

A new `Closure` library provides the theory-closure and audit toolkit (Group A):
observational semantics (`ObsSemantics`), world-types, selectors (sections of
the quotient), parameterized internality (`InternalPred`), audit soundness
(decidable-on-world-type ⇒ invariant), and the A0 bridge: when a theory has
internal representability (`TheoryWithInternalRepr`), it yields an `SRI'` instance
so that SelfReference's MFP-1 and diagonal barrier apply.  Zero sorrys, zero
custom axioms.  The Closure library includes: **Canonicalization** (gauge-fixing,
selector from canon), **Effective** (EffectiveSemantics, BoundedCover), **BoundedSelector**
(classical selector from bounded cover + canon; total bounded-search selector when
`DecidableEq WorldType`), and **Examples.FintypeWorld** (toy: finite worlds ⇒
effective semantics + bounded cover ⇒ selector).  See `Closure/Theorems/BoundedSelector.lean`
and `Closure/Examples/FintypeWorld.lean`.

### New sorrys (v2.2.0)

**5. `nems_rt_no_total_bool_decider` fixed-point step** (`SelfReference/Instances/NEMS.lean:96`):
The fixed point `∃ d, d = F d` for the negating transformer `F n := if decide n = true then false_n else true_n`.
Requires the Kleene recursion theorem for ℕ.  The NEMS diagonal barrier
is already proved without sorry in `NemS.Diagonal.Barrier` via the halting
reduction; this sorry is in the *abstract route* only.

**6. `lob` HBL chaining** (`SelfReference/Instances/Loeb.lean:56`):
The Hilbert–Bernays–Löb derivability conditions chaining in Löb's theorem.
The diagonal lemma step is fully proved.  The HBL chaining is standard
modal logic (Löb 1955, Boolos 1993).

---

### Sorry status

Seven `sorry` statements remain across three modules (plus 2 in SelfReference instances = 9 total):

**Quantum module (Paper 13):** Two sorrys in `NemS/Quantum/BuschGleason.lean`, encoding the
Busch/Gleason representation theorem existence direction:

1. **`delta_eq_zero_core`** (line ~971): The linear extension step showing that a POVM-additive
   measure μ on effects agrees with the trace functional Re(Tr(rhoCandidate·)) on all effects.
   This requires proving that POVM additivity + boundedness implies ℝ-linearity on the effect space,
   then using the fact that test effects span Herm(n) over ℝ.

2. **`rhoCandidate_psd`** (line ~985, inside the PSD proof): Positive semidefiniteness of rhoCandidate.
   Once representation is proved, PSD follows by applying representation to rank-1 projector effects
   |v><v|/||v||² and using μ.nonneg. The remaining `sorry` is the rank-1 projector construction
   (~80 lines of Hermitian/PSD/bounded proofs).

Both sorrys are precisely documented with complete mathematical specifications and references to
Busch (Phys. Rev. Lett. 91, 120403, 2003). The mathematical arguments are standard and not in dispute.
The Lean formalization requires ~200 additional lines of careful matrix algebra and 1D real analysis
(bounded additive functions on [0,1] vanishing on rationals must vanish everywhere).

**Reverse direction module (Paper 14):** Two sorrys in `NemS/ReverseBICS/BICS.lean` and
`NemS/ReverseBICS/BICS_Implies_NEMS.lean`, encoding the BICS ⇒ NEMS theorem:

3. **`bics_prob_bounded`** (NemS/ReverseBICS/BICS.lean:~56): Boundedness of Born probabilities
   Re(Tr(ρE)) ∈ [0,1] for effects E. Requires: PSD of ρ gives Re(Tr(ρE)) ≥ 0, and E ≤ I gives
   Re(Tr(ρE)) ≤ Tr(ρ) = 1.

4. **`bics_implies_nems`** (NemS/ReverseBICS/BICS_Implies_NEMS.lean:~33): The flagship reverse-direction
   theorem showing BICS (Born as internal complete semantics) implies NEMS (no external model selection).
   Requires: proof that BICS completeness (no external completion bits) forbids external selection.

**QuantumFinite bridge module (Paper 39 ↔ Paper 13):** Three sorrys in `GPTClosure/Instances/QuantumFinite.lean`,
bridging Paper 13's quantum formalization with Paper 39's GPT framework:

5. **PSD cone pointedness** (`quantumCone` pointedness): The PSD cone satisfies `x ∈ cone ∧ -x ∈ cone → x = 0`.
   Requires spectral argument: if both H and −H are PSD then all eigenvalues are zero, so H = 0.

6. **Born-rule nonnegativity** (inside `born_rule_is_gpt_prob`): For PSD ρ and PSD effect E,
   `Re(Tr(ρ * E)) ≥ 0`. Standard fact: trace of product of two PSD matrices is nonneg.

7. **Wiring to `busch_gleason_unique`** (inside `quantum_state_uniqueness`): Connecting the GPT
   uniqueness result to Paper 13's `busch_gleason_unique` theorem. Requires unpacking the
   `densityToState` / `quantumEffectToGPT` definitions to show agreement on all effects implies
   agreement on all test effects, then applying `busch_gleason_unique`.

**Quotient Section bridge (SPEC_68_IRS Target E):** **Complete** — `halting_framework_unbounded_world_types` and `halting_framework_no_computable_section` are fully proved (0 sorry). Build verified March 2026.

All structural definitions (`quantumCone`, `quantumOUS`, `bornMap`, `densityToState`,
`quantumEffectToGPT`, `povmToMeasurement`) and the Born-rule-equals-GPT-pairing theorem
(`born_rule_is_gpt_prob`) are fully proved (modulo the nonnegativity sorry above).
The module works around a Lean 4.29 instance search limitation with explicit `@` notation.

All other theorems in the library are fully proved without `sorry`, including:
- **Uniqueness**: `busch_gleason_unique` — if any ρ represents μ, it must be the unique one (0 sorrys)
- **Test-effect agreement**: rhoCandidate provably matches μ on all test effects D_k, R_ij, Q_ij (0 sorrys)
- **Delta infrastructure**: binary additivity, POVM-sum-zero, complement identity (0 sorrys)
- The full diagonal barrier, physical incompleteness, and determinism no-go chains (0 sorrys)
- The complete NEMS core, MFRR bridge, and PT non-effectiveness (0 sorrys)
- **SPEC_69 (summit):** QuotientSectionStrength — `halting_framework_no_decider_at_computable`, `halting_framework_no_total_computable_decider` (0 sorrys)

## Verified theorems

### Core (v1.0.0)

| File | Theorem | Statement |
|------|---------|-----------|
| `NemS/Core/Trichotomy.lean` | `nems_trichotomy` | Categorical ∨ internal selector ∨ needs external selection |
| `NemS/Core/Trichotomy.lean` | `nems_implies_cat_or_internal` | NEMS ⇒ categorical ∨ internal selector |
| `NemS/Core/Trichotomy.lean` | `nems_noncat_implies_internal` | NEMS + non-categorical ⇒ internal selector |
| `NemS/Reduction/ER.lean` | `er_non_categorical` | External dependency ⇒ non-categoricity in enlarged space |
| `NemS/Reduction/ER.lean` | `er_nems_forces_internal_selector` | NEMS on enlarged space ⇒ internal selector |
| `NemS/Reduction/ER.lean` | `nems_er_implies_detpsc` | NEMS + ER ⇒ determinacy-PSC |
| `NemS/Reduction/ER.lean` | `determinacyPSC_of_framework` | DeterminacyPSC holds for every framework |
| `NemS/Visibility/SemanticExternality.lean` | `semantic_externality_not_categorical` | Semantic externality ⇒ non-categoricity in F⁺ |
| `NemS/Visibility/SemanticExternality.lean` | `nems_forces_evaluator_selector` | NEMS forces internal selector for evaluator choices |
| `NemS/Meta/AuditProtocol.lean` | `passAudit_iff_nems` | PassAudit ↔ NEMS |
| `NemS/Core/Internality.lean` | `nems_definability` | NEMS under definability-internality |
| `NemS/Core/Internality.lean` | `nems_computability` | NEMS under computability-internality |
| `NemS/Core/Internality.lean` | `definability_implies_quotient_section` | Definability ⇒ quotient section exists |
| `NemS/Core/Internality.lean` | `selector_rigidity` | Definability-internal selectors commute with ObsEq-preserving maps (exported interface lemma for automorphism-invariance clause) |
| `NemS/Core/Internality.lean` | `summit_theorem_collapse` | Summit: ObsCategorical ∨ (∀ M N, ObsEq M N ↔ S.sel M = S.sel N) for definability-internal S |
| `NemS/Core/Internality.lean` | `SelectorSeparatesNonObsEq` | Predicate: selector separates non-ObsEq models |
| `NemS/Core/Internality.lean` | `selector_always_separates` | Every selector separates non-ObsEq models |
| `NemS/Core/Internality.lean` | `internal_selector_complete_invariant` | Under separation, selector equality classifies ObsEq exactly |
| `NemS/Core/Internality.lean` | `ObsAut` | Observational automorphism structure |
| `NemS/Core/Internality.lean` | `selector_rigidity_automorphism` | Definability-internal selector commutes with ObsAut |
| `NemS/Core/Internality.lean` | `selector_orbit_commutes` | Selector and automorphism actions commute on orbits |
| `NemS/Core/Selectors.lean` | `selector_eq_iff_obsEq` | Selector outputs classify ObsEq classes exactly: `S.sel M = S.sel N ↔ ObsEq M N` (complete invariant; no internality hypothesis needed) |
| `NemS/Core/Selectors.lean` | `selector_separation` | Separation direction: non-ObsEq inputs have distinct selector outputs |

### Diagonal Barrier (v2.0.0)

| File | Theorem | Statement |
|------|---------|-----------|
| `NemS/Diagonal/HaltingReduction.lean` | `asr_rt_computable_implies_halting_computable` | ASR + computable RT ⇒ computable halting |
| `NemS/Diagonal/HaltingReduction.lean` | `asr_rt_not_computable` | **ASR ⇒ RT not computable (diagonal barrier, Thm 5.9)** |
| `NemS/Diagonal/Barrier.lean` | `no_total_effective_rt_decider` | ASR ⇒ ¬ ComputablePred RT |
| `NemS/Diagonal/Instantiation.lean` | `halting_framework_rt_not_computable` | Concrete instantiation recovers halting undecidability |

### Quotient Section / SPEC_68_IRS, SPEC_69_DSL (v2.7.0)

| File | Theorem/Def | Statement |
|------|-------------|-----------|
| `NemS/Core/QuotientSection.lean` | `IsQuotientSection` | Section property: right inverse of toWorldType |
| `NemS/Core/QuotientSection.lean` | `EffectivePresentation` | Enum + surj + decidable ObsEq |
| `NemS/Core/QuotientSection.lean` | `BoundedCover` | Finite bound covering all world-types |
| `NemS/Core/QuotientSection.lean` | `bounded_cover_gives_computable_quotient_section` | **Target A:** Bounded cover ⇒ computable section |
| `NemS/Core/QuotientSection.lean` | `computable_section_implies_computable_selector` | **Target C:** Computable section ⇒ computable selector |
| `NemS/Core/QuotientSection.lean` | `effective_structure_gives_computable_selector` | Effective presentation + bounded cover ⇒ computable selector |
| `NemS/Core/QuotientSection.lean` | `definable_section_iff_definable_selector` | Definable section ↔ definable selector |
| `NemS/Core/QuotientSection.lean` | `exact_criterion_computable_section` | **Target D:** Computable section ↔ effective structure |
| `NemS/Core/QuotientSection.lean` | `no_total_effective_quotient_section_on_diagonal_fragment` | **Target E:** ASR + unbounded world-types ⇒ no computable section (bridge proved) |
| `NemS/Diagonal/QuotientSectionBridge.lean` | `partrec_singleton_halting` | Singleton halting function χₖ is partial recursive |
| `NemS/Diagonal/QuotientSectionBridge.lean` | `halting_framework_unbounded_world_types` | Halting framework has unboundedly many world-types |
| `NemS/Diagonal/QuotientSectionBridge.lean` | `halting_framework_no_computable_section` | Halting framework: no computably realizable quotient section |
| `NemS/Diagonal/QuotientSectionStrength.lean` | `halting_framework_no_decider_at_computable` | **SPEC_69:** Halting framework: no computable δ deciding nontrivial extensional T |
| `NemS/Diagonal/QuotientSectionStrength.lean` | `halting_framework_no_total_computable_decider` | General form: no computable decider for any extensional nontrivial T |

### MFRR Bridge (v2.0.0)

| File | Theorem | Statement |
|------|---------|-----------|
| `NemS/MFRR/ChoicePoints.lean` | `recordDivergentChoice_implies_not_obsCategorical` | Record-divergent choice ⇒ non-categoricity |
| `NemS/MFRR/ChoicePoints.lean` | `recordDivergentChoice_witness` | Extract disagreeing models from choice data |
| `NemS/MFRR/PSCBundle.lean` | `PSCBundle.cat_or_internal` | PSC ⇒ categorical ∨ internal selector |
| `NemS/MFRR/PTSelector.lean` | `nems_noncat_forces_PT` | NEMS + non-categorical ⇒ PT exists |
| `NemS/MFRR/PTSelector.lean` | `nems_cat_or_PT` | NEMS ⇒ categorical ∨ PT exists |
| `NemS/MFRR/DiagonalBarrier.lean` | `diagonal_barrier_rt` | **Diagonal-capable ⇒ RT not computable (zero axioms)** |
| `NemS/MFRR/DiagonalBarrier.lean` | `nems_noncat_forces_internal_and_diagonal_barrier` | NEMS + non-cat + diagonal ⇒ selector + undecidable RT |
| `NemS/MFRR/BridgeToNEMS.lean` | `PSC_and_choice_force_PT` | **PSC + record-divergent choice ⇒ PT exists** |
| `NemS/MFRR/BridgeToNEMS.lean` | `PSC_choice_diagonal_forces_constrained_selection` | **PSC + choice + diagonal ⇒ selector + undecidable RT** |
| `NemS/MFRR/BridgeToNEMS.lean` | `PSC_classification` | PSC + diagonal ⇒ categorical ∨ (selector ∧ undecidable RT) |
| `NemS/MFRR/BridgeToNEMS.lean` | `no_external_law` | PSC ⇒ ¬ NeedsExternalSelection |
| `NemS/MFRR/PTNonEffective.lean` | `pt_not_total_effective_on_RT` | **Diagonal-capable ⇒ PT not total-effective on RT** |
| `NemS/MFRR/PTNonEffective.lean` | `pt_exists_and_not_effective` | NEMS + non-cat + diagonal ⇒ ∃ PT, ¬ effective |
| `NemS/MFRR/ToyMFRR.lean` | `bool_PT_exists` | Bool framework: PT extracted via bridge theorem |
| `NemS/MFRR/ToyMFRR.lean` | `bool_has_divergent_choice` | Bool framework has record-divergent choice |

### Foundational Finality (Paper 23)

| File | Theorem | Statement |
|------|---------|-----------|
| `NemS/Reflexive/FinalityTheorem.lean` | `foundational_finality` | Master Loop T + MetaExplanation T' T ⇒ FailsPSC T' ∨ Redundant T' T ∨ Isomorphic T' T |
| `NemS/Reflexive/FinalityTheorem.lean` | `outside_dependence_exhaustion` | Same trilemma; named corollary packaging exhaustion of load-bearing outside explanations |
| `NemS/Reflexive/FinalityTheorem.lean` | `no_foundational_external_runner` | Alias for outside_dependence_exhaustion (Paper 78 synthesis) |
| `NemS/Reflexive/FinalityTheorem.lean` | `master_loop_fixed_point` | Master Loop T ⇒ Isomorphic (reconstruct (extract T)) T |

### Physical Incompleteness (Paper 11)

| File | Theorem | Statement |
|------|---------|-----------|
| `NemS/Physical/ASRFromUCT.lean` | `physUCT_implies_diagonalCapable` | PhysUCT ⇒ diagonal-capable (ASR) |
| `NemS/Physical/ASRFromUCT.lean` | `physUCT_implies_RT_not_computable` | PhysUCT ⇒ RT not computable |
| `NemS/Physical/ASRFromUCT.lean` | `physical_incompleteness` | Alias (Paper 78 synthesis): closed-universe no-total-effective-decider |
| `NemS/Physical/ASRFromUCT.lean` | `no_total_algorithmic_toe` | Alias: no total algorithmic theory of everything |

### Semantic Floor (Paper 24)

| File | Theorem | Statement |
|------|---------|-----------|
| `NemS/Cosmology/SemanticFloor.lean` | `semantic_floor` | DiagonalCapable + Universe ⇒ SatisfiesSemanticFloor |
| `NemS/Cosmology/SemanticFloor.lean` | `semantic_floor_theorem` | Alias (Paper 78 synthesis) |
| `NemS/Cosmology/SemanticFloor.lean` | `no_singularity_trap` | PSC + singularity-as-underspecification ⇒ False |
| `NemS/Cosmology/SemanticFloor.lean` | `no_singularity_as_underspecification` | Alias (Paper 78 synthesis) |

### Cosmological Closure Unification (Paper 78)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `NemS/Cosmology/UnifiedClosureFramework.lean` | `UnifiedClosureFramework` | Bridge ontology: one structure interpretable in all three theorem stacks |
| `NemS/Cosmology/UnifiedClosureFramework.lean` | `toCosmologicalFramework`, `toRecordFiltration`, `toNemSFramework` | Interpretation maps |
| `NemS/Cosmology/CosmologicalClosureSchema.lean` | `CosmologicalClosureSchema` | Diagonal + Universe + PSC (schema on unified base) |
| `NemS/Cosmology/Bridges/ToSemanticFloor.lean` | `ClosureAdmissibleInitiality` | Initial state satisfies semantic floor |
| `NemS/Cosmology/Bridges/ToSemanticFloor.lean` | `closure_schema_implies_admissible_initiality` | Schema ⇒ admissible initiality |
| `NemS/Cosmology/Bridges/ToArrowOfTime.lean` | `StructuralIrreversibility` | No-global-reversal (Paper 36) |
| `NemS/Cosmology/Bridges/ToArrowOfTime.lean` | `closure_schema_implies_structural_irreversibility` | Schema ⇒ irreversibility |
| `NemS/Cosmology/Bridges/ToFinality.lean` | `ClosureRealizedHistory` | ¬ NeedsExternalSelection |
| `NemS/Cosmology/Bridges/ToFinality.lean` | `closure_schema_implies_internal_realized_history` | Schema ⇒ no external selection |
| `NemS/Cosmology/Bridges/ToFoundationalFinality.lean` | `closure_schema_implies_outside_dependence_exhaustion` | Schema ⇒ outside-dependence exhaustion |
| `NemS/Cosmology/Bridges/ToFoundationalFinality.lean` | `cosmological_closure_unification_plus_finality` | Summit + fuller Finality |
| `NemS/Cosmology/Bridges/ToRecordResolution.lean` | `ucf_record_resolution_monotone` | UCF ⇒ record resolution H(t+1) ≥ H(t) (EPIC_66_SL2 Track 1) |
| `NemS/Cosmology/Bridges/ToHiddenHistoryEntropy.lean` | `ucf_fiberSize_le_under_forget`, `ucf_fiberSize_lt_under_strict_refinement` | EPIC_66_SL2 Track 2: fiber entropy decreases under refinement |
| `NemS/Cosmology/Bridges/ToGPTClosure.lean` | `GPTClosureStructureExists`, `gpt_closure_structure_exists` | Post-67 Phase 2: bridge to GPTClosure (Paper 39) |
| `NemS/Cosmology/Bridges/ToLawCalibration.lean` | `LawCalibrationStructureExists`, `law_calibration_structure_exists` | Post-67 Phase 3: bridge to LawCalibration (Paper 44) |
| `NemS/Cosmology/Bridges/ToAdjudicators.lean` | `strong_closure_schema_implies_adjudicator_infrastructure` | Strong schema + witness ⇒ adjudicator network |
| `NemS/Cosmology/CosmologicalClosureUnification.lean` | `cosmological_closure_unification` | **Grand unification:** Schema ⇒ admissible ∧ irreversible ∧ internal realized |
| `NemS/Cosmology/FoundationalAdmissibility.lean` | `FoundationallyViable`, `ClosureCompatible` | EPIC_67_FA: viability classification predicates |
| `NemS/Cosmology/FoundationalAdmissibility.lean` | `foundational_admissibility` | ClosureCompatible ⇒ FoundationallyViable |
| `NemS/Cosmology/FoundationalAdmissibility.lean` | `foundationally_viable_implies_closure_compatible` | **Converse:** FoundationallyViable ⇒ ClosureCompatible |
| `NemS/Cosmology/FoundationalAdmissibility.lean` | `viability_failure_implies_not_closure_compatible` | ¬FoundationallyViable ⇒ ¬ClosureCompatible |
| `NemS/Cosmology/FoundationalAdmissibility.lean` | `SurvivorCompatible`, `ProbabilisticallyAdmissible`, `PhysicsArchitectureAdmissible` | Post-67 cascade predicates |
| `NemS/Cosmology/FoundationalAdmissibility.lean` | `survivor_compatible_implies_foundationally_viable` | SurvivorCompatible ⇒ FoundationallyViable |
| `NemS/Cosmology/FoundationalAdmissibility.lean` | `survivor_compatible_implies_probabilistically_admissible` | SurvivorCompatible ⇒ ProbabilisticallyAdmissible |
| `NemS/Cosmology/FoundationalAdmissibility.lean` | `ClosureForcedProbabilityStructure` | Paper 80: U-relative ObsEq-respecting GPT interpretation |
| `NemS/Cosmology/FoundationalAdmissibility.lean` | `ClosureCalibratedLawStructure` | Paper 80: U-relative InitState → Law with fixed points |
| `NemS/Cosmology/FoundationalAdmissibility.lean` | `survivor_compatible_implies_closure_forced_probability_structure` | SurvivorCompat ⇒ ClosureForcedProbabilityStructure |
| `NemS/Cosmology/FoundationalAdmissibility.lean` | `foundationally_viable_implies_closure_calibrated_law_structure` | FoundationallyViable ⇒ ClosureCalibratedLawStructure |
| `NemS/Cosmology/FoundationalAdmissibility.lean` | `foundationally_viable_implies_physics_architecture_admissible` | FoundationallyViable ⇒ PhysicsArchitectureAdmissible (structure-tied) |
| `NemS/Cosmology/Bridges/ToGPTClosure.lean` | `UCFHasObsEqRespectingGPTInterpretation` | U-relative ι : World → State (ToySpace 1) respecting ObsEqAt |
| `NemS/Cosmology/ClassificationCascade.lean` | `CascadeCompatible` | FoundationallyViable ∧ ProbabilisticallyAdmissible ∧ PhysicsArchitectureAdmissible |
| `NemS/Cosmology/ClassificationCascade.lean` | `NarrowSurvivorClass` | CascadeCompatible ∧ Inhabited World (genuine narrowing) |
| `NemS/Cosmology/ClassificationCascade.lean` | `probabilistic_and_physical_filter` | SurvivorCompatible ⇒ ProbabilisticallyAdmissible ∧ PhysicsArchitectureAdmissible |
| `NemS/Cosmology/ClassificationCascade.lean` | `survivor_compatible_implies_cascade_compatible` | SurvivorCompatible ⇒ CascadeCompatible |
| `NemS/Cosmology/ClassificationCascade.lean` | `survivor_filter_narrows_class` | SurvivorCompatible ∧ Inhabited World ⇒ NarrowSurvivorClass |
| `NemS/Cosmology/UnifiedClosureFramework/Examples/Toy.lean` | `toyUnified`, `unified_framework_inhabited` | Structural nonvacuity witness |
| `NemS/Cosmology/StrongCosmologicalClosureSchema.lean` | `StrongCosmologicalClosureSchema` | Base schema + GRS + NCC (Paper 17) |

CosmologicalClosureUnification: **0 sorry**. Full grand theorem discharged. Extension A: stronger finality corollary (`cosmological_closure_unification_plus_finality`). Extension B: strong schema and adjudicator bridge under witness. EPIC_66_SL2: record resolution monotonicity bridge (`ucf_record_resolution_monotone`). EPIC_67_FA: FoundationalAdmissibility — **equivalence proved**: FoundationallyViable ↔ ClosureCompatible (foundational_admissibility, foundationally_viable_implies_closure_compatible, viability_failure_implies_not_closure_compatible). Paper 80: ClassificationCascade with structure-tied predicates (ClosureForcedProbabilityStructure, ClosureCalibratedLawStructure), NarrowSurvivorClass, survivor_filter_narrows_class.

### Reverse Direction: BICS ⇒ NEMS ⇒ PSC (v2.1.0, Paper 14)

| File | Theorem | Statement |
|------|---------|-----------|
| `NemS/ReverseBICS/BICS.lean` | `BICS` structure | Born Internal & Complete Semantics definition |
| `NemS/ReverseBICS/BICS_Implies_NEMS.lean` | `bics_implies_nems` | **BICS ⇒ NEMS (reverse direction flagship)** |
| `NemS/ReverseBICS/BICS_Implies_NEMS.lean` | `bics_rules_out_external` | BICS ⇒ ¬ NeedsExternalSelection |

### Closure (v2.2.0, Paper 27)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `Closure/Theorems/AuditSoundness.lean` | `audit_soundness` | Decidable-on-world-type ⇒ invariant |
| `Closure/Theorems/AuditSoundness.lean` | `not_invariant_implies_not_decidable_on_world_type` | ¬ invariant ⇒ ¬ decidable on world-type |
| `Closure/Theorems/BoundedSelector.lean` | `boundedSelectorClassical` | Selector from BoundedCover + Canonicalization (classical) |
| `Closure/Theorems/BoundedSelector.lean` | `nonempty_selector_of_bounded_cover` | BoundedCover + Canonicalization ⇒ Nonempty (Selector) |
| `Closure/Theorems/BoundedSelector.lean` | `boundedSelectorAsSelector` | Total selector by bounded search when DecidableEq WorldType |
| `Closure/Examples/FintypeWorld.lean` | `effectiveSemanticsOfFintype` | Fintype World + DecidableRel ObsEquiv ⇒ EffectiveSemantics |
| `Closure/Examples/FintypeWorld.lean` | `boundedCoverOfFintype` | Fintype ⇒ BoundedCover (cover = Fintype.card) |
| `Closure/Examples/FintypeWorld.lean` | `selectorOfFintypeWorld` | Fintype world ⇒ selector (nailed constructive instance) |

### Reflection (v2.3.0, Paper 28)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `Reflection/Core/SRI_R.lean` | `SRI_R` class | Restricted repr: repr only for F ∈ R |
| `Reflection/Core/SRI_R.lean` | `DiagClosed` | R closed under diagonalization template |
| `Reflection/Core/SRI_R.lean` | `sri0'_to_sri_r` | SRI₀′ induces SRI_R with R = allRepresentable |
| `Reflection/Theorems/DiagonalClosure.lean` | `restricted_master_fixed_point` | **Diagonal Closure Theorem**: DiagClosed R ⇒ ∀F∈R, ∃p, p ≃ F(quote p) |
| `Reflection/Hierarchy/Examples.lean` | `allRepresentable_restricted_fixed_point` | Recovery: R = allRepresentable ⇒ full MFP-1 |
| `Reflection/Hierarchy/Separation.lean` | `not_diagClosed_identity_only` | R = {id} is not diagonally closed |
| `Reflection/Hierarchy/Separation.lean` | `method_level_separation` | ∃ F ∈ R such that G_F ∉ R (identity-only) |

### SelectorStrength (v2.4.0, Paper 29)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `SelectorStrength/Core/Strength.lean` | `Strength`, `Strength.le` | Strength as predicate on functions; preorder |
| `SelectorStrength/Core/Deciders.lean` | `TotalDecider`, `DecidableAt`, `Extensional`, `Nontrivial` | Deciders and extensional predicates |
| `SelectorStrength/Core/AntiDecider.lean` | `antiDecider`, `AntiDeciderClosed` | Anti-decider transformer and closure |
| `SelectorStrength/Theorems/BarrierSchema.lean` | `no_total_decider_at_strength` | **Barrier schema**: AntiDeciderClosed + hFP ⇒ ¬ DecidableAt Sbool T |
| `SelectorStrength/Theorems/Monotonicity.lean` | `decidableAt_mono` | S₁ ≤ S₂ ⇒ DecidableAt S₁ T → DecidableAt S₂ T |
| `SelectorStrength/Bridge/Reflection.lean` | `reflection_supplies_hFP` | DiagClosed R ⇒ fixed-point premise for barrier |
| `SelectorStrength/Bridge/Closure.lean` | `SelectorAt`, `selectorAt_mono` | Selector at strength S; monotonicity |
| `SelectorStrength/Instances/Trivial.lean` | `S_all`, `no_total_decider_all` | Trivial strength (all functions); barrier corollary |
| `SelectorStrength/Instances/ComputableNat.lean` | `no_total_decider_nat` | Barrier for Nat at parametric strength (Sbool, Sα) |

### Learning (v2.5.0, Paper 30)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `Learning/Core/Certificates.lean` | `Claim`, `TotalDecider`, `Extensional`, `Nontrivial` | Certificate/claim vocabulary (re-exports Deciders) |
| `Learning/Core/SelfTrust.lean` | `SelfCertifierAtStrength`, `selfCertifierAtStrength_iff` | Self-certifier at strength S |
| `Learning/Theorems/SelfTrustBarrier.lean` | `no_total_self_certifier` | **No total internal self-certifier**: Extensional + Nontrivial + AntiDeciderClosed + hFP ⇒ ¬ DecidableAt Sbool Claim |
| `Learning/Theorems/SelfTrustBarrier.lean` | `no_self_certifier_at_strength` | Same theorem phrased as no self-certifier at strength |
| `Learning/Bridge/Reflection.lean` | `reflection_supplies_hFP_for_learning` | DiagClosed R + quote=id ⇒ fixed point for barrier |
| `Learning/Bridge/Reflection.lean` | `barrier_premise_from_reflection` | DiagClosed R + quote=id ⇒ hFP for all F ∈ R |
| `Learning/Examples/ToyGuarantee.lean` | `ToyClaim`, `toyClaim_extensional`, `toyClaim_nontrivial` | Toy claim (n=0 on ℕ); extensional, nontrivial |
| `Learning/Examples/ToyGuarantee.lean` | `no_total_self_certifier_toy` | Barrier applies to ToyClaim when hFP present |
| `Learning/Positive/Stratified.lean` | `stratified_self_certification_toy` | **Stratified self-certification**: DecidableAt S_all ToyClaim (when hFP not assumed) |

Learning library: **0 sorry**, 0 custom axioms. Composes with SelectorStrength and Reflection.

### EpistemicAgency (v2.6.0, Paper 31)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `EpistemicAgency/Core/ClaimDomain.lean` | Claim domain, coverage | Finite claim domain and certified coverage |
| `EpistemicAgency/Core/Agent.lean` | Agent, verifier | Agent as verifier; no universal total self-certifier (imported from Learning) |
| `EpistemicAgency/Core/Protocol.lean` | Protocol, Admissible | Verification protocol; admissible = no hallucination where all abstain |
| `EpistemicAgency/Theorems/NoSelfCertifierImported.lean` | Agency theorem | Diagonal-capable agent has no universal total internal self-certifier (Paper 30) |
| `EpistemicAgency/Theorems/ProtocolStrictImprovement.lean` | Strict separation | ∃ society and protocol with certified coverage strictly larger than any individual verifier |
| `EpistemicAgency/Theorems/Diversity.lean` | Diversity necessity | Homogeneous societies cannot strictly improve; role diversity necessary for strict improvement |
| `EpistemicAgency/Theorems/MetaBarrier.lean` | Meta-barrier | Society+protocol as single diagonal-capable system ⇒ Paper 30 barrier reappears at societal level |
| `EpistemicAgency/Examples/ToySociety.lean` | Toy society | Concrete toy instance |

EpistemicAgency library: **0 sorry**, 0 custom axioms. Composes with Learning (Paper 30).

### SelfImprovement (v2.7.0, Paper 32)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `SelfImprovement/Core/Upgrades.lean` | Agent, Upgrade, UpCert, Good | Upgrade certificates and good-predicate vocabulary |
| `SelfImprovement/Theorems/Barrier.lean` | `no_total_upgrade_certifier` | **No total upgrade certifier**: Extensional + Nontrivial + AntiDeciderClosed + hFP ⇒ ¬ DecidableAt (Paper 30 applied to upgrades) |
| `SelfImprovement/Theorems/Stratified.lean` | `stratified_improvement_schema` | Stratified positive result (barrier contrapositive) |
| `SelfImprovement/Theorems/SocietyImproves.lean` | `protocol_strict_improvement_upgrades`, `diversity_necessary_upgrades` | Protocol strict improvement; diversity necessary (uses EpistemicAgency) |
| `SelfImprovement/Theorems/MetaBarrier.lean` | `meta_barrier_self_improvement` | Meta-barrier for self-improvement (society+protocol as single system) |
| `SelfImprovement/Examples/ToyUpgrades.lean` | Toy upgrades | Toy instance (EpistemicAgency.toyDomain, toySociety) |

SelfImprovement library: **0 sorry**, 0 custom axioms. Composes with Learning, EpistemicAgency.

### SelfAwareness (v2.8.0, Paper 33)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `SelfAwareness/Core/ClaimFamilies.lean` | ClaimLang, SelfAwareAt | Claim languages, self-awareness at strength, classes C₀/C₁/C₂ |
| `SelfAwareness/Core/SelfModel.lean` | Fix, MultipleFixedPoints | Self-model update, fixed points, multiplicity |
| `SelfAwareness/Theorems/Hierarchy.lean` | `no_total_certifier_C2` | **No total certifier for C₂** under diagonal capability (Paper 30 barrier) |
| `SelfAwareness/Theorems/SelectorNecessity.lean` | `selection_not_total_effective`, `selector_necessary_from_multiplicity` | Multiplicity ⇒ selector necessity; selection barrier |
| `SelfAwareness/Theorems/IntrospectiveOptimality.lean` | `no_total_rightness_certifier` | No total rightness certifier under diagonal capability; stratified positive results |
| `SelfAwareness/Examples/ToyHierarchy.lean` | `base_certifier_exists` | Concrete claim ladder (C₀ has total certifier) |
| `SelfAwareness/Examples/ToyMultiplicity.lean` | `toy_multiple_fixed_points` | Two indistinguishable fixed points toy (Fin 2, identity update) |
| `SelfAwareness/Examples/ToyRightness.lean` | `stratified_rightness_toy` | Finite rightness toy (stratified certifier exists) |

SelfAwareness library: **0 sorry**, 0 custom axioms. Composes with Learning, Closure, Reflection, SelectorStrength.

### Sieve (v2.9.0, Paper 34)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `Sieve/Core/TheorySpace.lean` | `TheorySpace` | Type of candidates with optional Equiv and canon |
| `Sieve/Core/Constraints.lean` | `Constraint`, `SieveHolds`, `Residual` | Constraint = α → Prop; sieve = List.Forall; residual = { a // SieveHolds cs a } |
| `Sieve/Theorems/Residual.lean` | `sieve_sublist` | cs.Sublist cs' ∧ SieveHolds cs' a → SieveHolds cs a |
| `Sieve/Theorems/Residual.lean` | `residual_mono` | Monotonicity: more constraints ⇒ smaller residual |
| `Sieve/Theorems/Residual.lean` | `pullbackConstraints` | Pullback of constraint list along f : α → β |
| `Sieve/Theorems/Residual.lean` | `sieve_pullback` | SieveHolds (pullback f ds) a ↔ SieveHolds ds (f a) (functoriality) |
| `Sieve/Examples/ToyDomain.lean` | `toySpace`, `toySieve`, `toy_residual_nonempty` | Toy: Fin 3, two constraints, certified residual witness |

Sieve library: **0 sorry**, 0 custom axioms. Composes with NemS.Prelude; reusable for gauge theory, oracles, and other theory-space classifications.

### Hypercomputation (Paper 35)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `Hypercomputation/Core/OracleAsSelector.lean` | `AuditPassesFor`, `SelectorSensitive` | Oracle-as-selector audit vocabulary |
| `Hypercomputation/Core/HypercomputerClaim.lean` | `HypercomputerClaim`, `HasInternalHypercomputerAt` | Hypercomputer claim interface |
| `Hypercomputation/Theorems/NoInternalHypercomputer.lean` | `no_internal_hypercomputer_at_strength` | Under AntiDeciderClosed + hFP, no total internal hypercomputer for extensional nontrivial T |
| `Hypercomputation/Theorems/Taxonomy.lean` | `internal_hypercomputer_claim_forces_premise_failure` | Any internal hypercomputer claim forces failure of at least one barrier premise |
| `Hypercomputation/Examples/Halting.lean` | `no_internal_hypercomputer_for_halting` | Halting example |
| `Hypercomputation/Examples/RecordTruth.lean` | `no_internal_hypercomputer_for_record_truth` | Record-truth example |

Hypercomputation library: **0 sorry**, 0 custom axioms. Composes with Closure, Reflection, SelectorStrength, and NemS diagonal modules.

### ArrowOfTime (Paper 36)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `ArrowOfTime/Core/RecordFiltration.lean` | RecordFiltration, Visible, ObsEqAt, WorldTypeAt | Time-indexed record filtration; stage equivalence and stage world-types |
| `ArrowOfTime/Core/Refinement.lean` | forget | Forgetful map WorldTypeAt (t+1) → WorldTypeAt t |
| `ArrowOfTime/Theorems/ArrowRefinement.lean` | `strict_refinement` | Strict record growth at t ⇒ forget not injective |
| `ArrowOfTime/Theorems/NoOverwrite.lean` | OverwriteAt, `no_overwrite_implies_not_categorical` | Overwrite at stage t ⇒ ¬ CategoricalAt t |
| `ArrowOfTime/Theorems/Irreversibility.lean` | `no_global_reversal` | Stage-preserving involution fixes world-types |
| `ArrowOfTime/Theorems/ClosureArrow.lean` | `closure_arrow_theorem` | **Paper 78:** Stable records + closure ⇒ structural irreversibility (wrapper) |
| `ArrowOfTime/Theorems/SelectionBarrier.lean` | `selection_barrier_retrodiction` | Under hFP + AntiClosed, retrodiction selector ruled out |
| `ArrowOfTime/Examples/Toy.lean` | filt, toy_strict_growth, toy_no_overwrite_witness | Toy: two bits; strict refinement; overwrite ⇒ not categorical |

ArrowOfTime library: **0 sorry**, 0 custom axioms. Composes with Closure, SelectorStrength.

### ChronologyUnderClosure (Paper 37)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `ChronologyUnderClosure/Core/RecordDynamics.lean` | Feedback, SelfConsistent, Overwrite | Record dynamics; self-consistent loop = fixed point mod ObsEquiv; overwrite = o holds at w, not at F(w) |
| `ChronologyUnderClosure/Theorems/RecordNonOverwrite.lean` | `record_non_overwrite` | Overwrite (w, o) → ¬ Categorical (branching) |
| `ChronologyUnderClosure/Theorems/SelectionBarrier.lean` | `selection_barrier_chronology`, `loopPred_extensional` | Under hFP + AntiClosed, "which loop" indicator not in Sbool; loop predicate extensional |

ChronologyUnderClosure library: **0 sorry**, 0 custom axioms. Composes with Closure, SelectorStrength.

### BlackHoles (Paper 38)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `BlackHoles/Core/RecordFragments.lean` | ErasingAppearance, `record_consistency_abstract` | Erasing appearance ⇒ ¬ Categorical (selection required); selector exists classically |
| `BlackHoles/Theorems/NoHypercomputingFromBH.lean` | `no_hypercomputing_from_bh` | Under barrier premises, no total decider at Sbool for nontrivial extensional T (no BH decoder) |

BlackHoles library: **0 sorry**, 0 custom axioms. Composes with SelectorStrength.

### GPTClosure (Paper 39)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `GPTClosure/Core/OrderedSpaces.lean` | Ordered unit space, cone | Finite-dimensional ordered unit space $(V, V_+, u)$ |
| `GPTClosure/Core/EffectsStates.lean` | Effects, states, prob | Effects $0 \le e \le u$; states as positive linear functionals; $\mathsf{prob}$ |
| `GPTClosure/Core/Measurements.lean` | Measurements | Measurements as unit decompositions |
| `GPTClosure/Theorems/Uniqueness.lean` | `state_ext_effect_span`, `uniqueness_under_spanning` | States determined by agreement on effects; unique extension when effects span $V$ |
| `GPTClosure/Theorems/ClosurePrinciples.lean` | `ClosureAssignment`, `closure_implies_affine_linear` | Closure principles ⇒ unique affine/linear state functional |
| `GPTClosure/Examples/Toy.lean` | Toy | Classical simplex; closure axioms hold |
| `GPTClosure/Instances/QuantumFinite.lean` | `quantumCone`, `quantumOUS` | PSD cone as ordered unit space (1 sorry: pointedness) |
| `GPTClosure/Instances/QuantumFinite.lean` | `bornMap`, `densityToState` | Born map and density-to-GPT-state embedding |
| `GPTClosure/Instances/QuantumFinite.lean` | `quantumEffectToGPT` | Quantum effects ↪ GPT effects |
| `GPTClosure/Instances/QuantumFinite.lean` | `born_rule_is_gpt_prob` | **Born rule = GPT state-effect pairing** (1 sorry: nonnegativity) |
| `GPTClosure/Instances/QuantumFinite.lean` | `povmToMeasurement` | POVMs ↪ GPT measurements |
| `GPTClosure/Instances/QuantumFinite.lean` | `quantum_state_uniqueness` | Quantum state uniqueness via GPT uniqueness (1 sorry: wiring to busch_gleason_unique) |

GPTClosure core library: **0 sorry**, 0 custom axioms. GPTClosure/Instances/QuantumFinite: **3 sorry** (PSD cone pointedness, Born-rule nonnegativity, wiring to busch_gleason_unique). Standalone (Paper 39: probability as closure in GPTs; QuantumFinite bridges Paper 13 ↔ Paper 39).

### InstitutionalEpistemics (Paper 40)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `InstitutionalEpistemics/Core/Roles.lean` | Role, coverage, diversity | Roles and coverage sets; role equivalence |
| `InstitutionalEpistemics/Core/ThreatModel.lean` | Instance space, adversary | Threat model, attack surface |
| `InstitutionalEpistemics/Core/Protocols.lean` | Protocol, Admissible | Protocol aggregates verifiers; admissibility (no hallucination) |
| `InstitutionalEpistemics/Theorems/NoUniversalJudge.lean` | `no_universal_final_judge` | Under anti-decider closure and hFP, no institution is total+sound+complete on nontrivial claims |
| `InstitutionalEpistemics/Theorems/LowerBounds.lean` | `k_role_lower_bound` | $k$-way partition + role-type constraint ⇒ full certified coverage needs ≥ $k$ roles |
| `InstitutionalEpistemics/Theorems/RobustnessImprovement.lean` | `diversity_necessity` | Strict robustness improvement ⇒ at least two non-equivalent roles |
| `InstitutionalEpistemics/Examples/ToyRegulation.lean` | Toy | Explicit toy witness for k-role bound |

InstitutionalEpistemics library: **0 sorry** in core/theorems, **1 sorry** in CosmicAudit.Examples.ToyCosmic (`toy_strict_improvement` match-branch proof); 0 custom axioms. Composes with Learning, EpistemicAgency, SelectorStrength.

**CosmicAudit (Paper 49)** lives inside InstitutionalEpistemics: `CosmicAudit/Core/Contexts.lean`, `Core/ForcedNetwork.lean`, `Theorems/ForcedAdjudication.lean`, `Theorems/DiversityLift.lean`, `Examples/ToyCosmic.lean`. T49.1 `forced_distributed_adjudication`, T49.2 `diversity_necessary_strict_improvement` (re-export Paper 40).

### RefinementFlow (Paper 41)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `RefinementFlow/Core/RefinementFlow.lean` | `forgetFromTo` | Iterated forget: WorldTypeAt t' → WorldTypeAt t when t ≤ t' |
| `RefinementFlow/Core/RefinementFlow.lean` | `forgetFromTo_succ` | One-step case: forgetFromTo t (t+1) = forget (Paper 36) |
| `RefinementFlow/Core/RefinementFlow.lean` | `forgetFromTo_coherent` | forgetFromTo t t' h (toWorldTypeAt t' w) = toWorldTypeAt t w |
| `RefinementFlow/Core/RefinementFlow.lean` | `forgetFromTo_naturality` | forgetFromTo t t' ∘ forgetFromTo t' t'' = forgetFromTo t t'' when t ≤ t' ≤ t'' |
| `RefinementFlow/Examples/ToyBits.lean` | `toy_strict_growth`, `toy_forgetFromTo_01` | Toy two-bit world; strict growth at 0; coherence of forgetFromTo 1→0 |

RefinementFlow library: **0 sorry**, 0 custom axioms. Composes with ArrowOfTime (Paper 36).

### RecordEntropy (Paper 42)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `RecordEntropy/Core/EntropyFinite.lean` | `recordEntropy` | H(t) = card(WorldTypeAt t) for finite case |
| `RecordEntropy/Theorems/Monotonicity.lean` | `recordEntropy_monotone` | H(t+1) ≥ H(t) |
| `RecordEntropy/Theorems/Monotonicity.lean` | `recordEntropy_strict` | StrictGrowthAt t ⇒ H(t+1) > H(t) |
| `RecordEntropy/Theorems/NoncomputabilityBarrier.lean` | `entropyClaim` | T(n) := (H(t) = n) (fixed-instance) |
| `RecordEntropy/Theorems/NoncomputabilityBarrier.lean` | `no_total_decider_entropy` | AntiDeciderClosed + hFP ⇒ ¬ DecidableAt Sbool T |
| `RecordEntropy/Theorems/UniformEntropyBarrier.lean` | `EntropyCode`, `entropyOfCode` | Code encoding (filtration, t, n); entropy of encoded instance |
| `RecordEntropy/Theorems/UniformEntropyBarrier.lean` | `uniformEntropyClaim`, `no_total_decider_uniform_entropy` | **Uniform barrier**: no total decider for T on codes |
| `RecordEntropy/Examples/ToyEntropy.lean` | `toy_entropy_monotone`, `toy_entropy_strict` | Toy: monotone, strict at t=0 |
| `RecordEntropy/Examples/ToyEntropy.lean` | `toy_no_total_decider_entropy` | Barrier applies to Toy entropy claim (fixed-instance) |

RecordEntropy library: **0 sorry**, 0 custom axioms. Composes with ArrowOfTime, RefinementFlow, SelectorStrength.

### ErrorCorrectingClosure (Paper 43)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `ErrorCorrectingClosure/Core/DecodingModel.lean` | `InstanceIndex`, `DecodeCode`, `isConsistent`, `decoderClaim` | Codes (instance, claimed); uniform decoder-claim predicate |
| `ErrorCorrectingClosure/Theorems/DecoderBarrier.lean` | `decoderClaim_extensional`, `decoderClaim_nontrivial` | Decoder-claim extensional and nontrivial |
| `ErrorCorrectingClosure/Theorems/DecoderBarrier.lean` | `no_total_decider_decoder_claim` | **Decoder barrier**: AntiDeciderClosed + hFP ⇒ ¬ DecidableAt Sbool decoderClaim |
| `ErrorCorrectingClosure/Theorems/ProtocolImprovement.lean` | `decodingCoverage`, `StrictDecodingImprovement`, `diversity_necessity_decoding` | Wrapper over Paper 40: strict decoding improvement ⇒ diversity |
| `ErrorCorrectingClosure/Examples/ToyDecoder.lean` | `toy_decoder_claim_nontrivial`, `toy_no_total_decider_decoder` | Toy: two instance types; barrier applies |

ErrorCorrectingClosure library: **0 sorry**, 0 custom axioms. Composes with SelectorStrength, InstitutionalEpistemics.

### LawCalibration (Paper 44)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `LawCalibration/Core/LawUpdate.lean` | `Law`, `lawUpdate`, `IsFixedPoint`, `IsMinimalFixedPoint`, `LawCode`, `lawSelectorClaim` | Law type, update U, fixed points; toy single-instance claim (not barrier target) |
| `LawCalibration/Core/LawUpdate.lean` | `InstanceIndex`, `LawInstanceCode`, `isMinimalForInstance`, `uniformLawSelectorClaim` | **Uniform** codes (instance, candidate, claimed); uniform predicate |
| `LawCalibration/Theorems/LawFixedPoints.lean` | `all_fixed`, `fixed_point_exists`, `fixed_point_multiplicity`, `minimal_fixed_point` | Every element fixed; multiplicity (two distinct fixed points) |
| `LawCalibration/Theorems/LawSelectionBarrier.lean` | `uniformLawSelectorClaim_extensional`, `uniformLawSelectorClaim_nontrivial` | Uniform law-selector claim extensional and nontrivial |
| `LawCalibration/Theorems/LawSelectionBarrier.lean` | `no_total_decider_uniform_law_selector` | **Law selection barrier (uniform)**: AntiDeciderClosed + hFP on LawInstanceCode ⇒ ¬ DecidableAt Sbool uniformLawSelectorClaim |
| `LawCalibration/Examples/ToyLaw.lean` | `toy_fixed_point_multiplicity`, `toy_lawSelectorClaim_nontrivial`, `toy_no_total_decider_uniform_law_selector` | Toy: multiplicity and concept; barrier re-exported for uniform predicate |

LawCalibration library: **0 sorry**, 0 custom axioms. Composes with SelectorStrength.

### SemanticNonlocality (Paper 45)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `SemanticNonlocality/Core/LocalityAxioms.lean` | `LocalityAxioms`, `Factorized`, `same_local_views_imp_obs_equiv` | Fragment, LocalWorld, restrict, localHolds; factorized ⇒ same local views ⇒ ObsEquiv |
| `SemanticNonlocality/Theorems/LocalDynamicsNotLocalSemantics.lean` | `same_local_views_imp_same_world_type` | Same local views ⇒ same world-type (global gluing) |
| `SemanticNonlocality/Examples/ToyFactorization.lean` | `toySemantics`, `toyLocality`, `toy_same_views_obs_equiv` | Toy: two fragments, Boolean local views; factorization and main theorem |

SemanticNonlocality library: **0 sorry**, 0 custom axioms. Depends on Closure.Core.ObsSemantics.

### CausalNonlocality (Paper 46)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `CausalNonlocality/Theorems/NoGo.lean` | `no_local_semantic_determinacy` | No-go: under barrier (anti-decider + hFP), no total decider for extensional nontrivial T (local semantic determinacy impossible). |
| `CausalNonlocality/Examples/ToyNoGo.lean` | `ToyT`, `toy_no_go` | Barrier witness on Nat; theorem parametric in hFP (0 axioms; instantiate hFP from Reflection/Partrec for concrete no-go). |

CausalNonlocality library: **0 sorry**, **0 custom axioms**. Depends on SelectorStrength. Barrier witness is parametric in the fixed-point premise.

### CertificationLogic (Paper 50)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `CertificationLogic/Core/InstanceSemantics.lean` | Verdict, Verifier, coverage, canonicalVerifier | Instance semantics and coverage |
| `CertificationLogic/Core/Protocols.lean` | Prot (atom, union, inter, prefer), atoms, protocolCoverage, `protocolCoverage_subset_union_atoms` | Protocol terms; normal form: coverage ⊆ union of atoms |
| `CertificationLogic/Core/Formulas.lean` | Formula, Derivable, axFromCov | Claim sets; Ax, Union, Subset, StratumMono |
| `CertificationLogic/Core/CertifiableAt.lean` | CertifiableAt, ConsistentWith, canonicalRoleAssign | Semantic certifiability |
| `CertificationLogic/Theorems/CapstoneSoundness.lean` | `soundness_capstone` | **T50.1:** ⊢_S C ⇒ CertifiableAt(S, C) |
| `CertificationLogic/Theorems/CapstoneCompleteness.lean` | `completeness_capstone`, `derivable_coverage` | **T50.2:** CertifiableAt(S, C) ⇒ ⊢_S C (via normal form) |
| `CertificationLogic/Theorems/Maximality.lean` | `boundary_maximality` | **T50.3:** Under barrier premises, no total decider for extensional nontrivial T |
| `CertificationLogic/Examples/ToyFinite.lean` | `toy_equiv` | Fin 4 toy: ⊢ C ↔ CertifiableAt(C) |
| `CertificationLogic/Examples/ToyBoundary.lean` | `toy_boundary` | Nat boundary toy (parametric in hFP) |

CertificationLogic library: **0 sorry**, 0 custom axioms. Depends on InstitutionalEpistemics.Core.Roles, SelectorStrength. Build: full `lake build` from nems-lean root (do not build CertificationLogic alone). See NEMS_LEAN_BUILD_NOTE.md.

### SemanticSelfDescription (Paper 51)

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `SemanticSelfDescription/Core/Claims.lean` | Claim, Code, Decode, RealizedTrue, ClaimEquiv, CodeEquiv | Self-semantic frame vocabulary |
| `SemanticSelfDescription/Core/Claims.lean` | `false_of_encodedNontrivial_indiscrete_CodeEquiv` | Universal `CodeEquiv` forbids `EncodedNontrivial` |
| `SemanticSelfDescription/Core/SelfTheory.lean` | SelfTheory, FinalSelfTheory, Internal, TotalOn, ExactOn | Final self-theory definition |
| `SemanticSelfDescription/Core/SelfScope.lean` | SelfScoped, StronglySelfScoped | Self-scoped claims |
| `SemanticSelfDescription/Core/SelfErasure.lean` | WeakSelfErasing, StrongSelfErasing | Weak and strong self-erasure |
| `SemanticSelfDescription/Theorems/NoFinalSelfTheory.lean` | `no_final_self_theory`, `BarrierHypothesesPred`, `toBarrierHypotheses`, `no_final_self_theory'` | **Flagship:** ¬ final internal self-theory from unconditional `hFP`; predicated Rogers + coercion when `∀ F', P F'` |
| `SemanticSelfDescription/Bridge/AugmentBarrierHypotheses.lean` | `barrierHypotheses_augment_withGlobalConjunct`, `barrierHypothesesPred_augment_withGlobalConjunct` | Global `(U₁)`-style conjunct on `BarrierHypotheses` / `BarrierHypothesesPred` |
| `SemanticSelfDescription/Instances/KleenePartrec.lean` | `kleenePartrecFrame`, `kleeneCodeEquiv`, `kleeneComputationalBarrierHypotheses` | Concrete `Nat.Partrec.Code` frame; extensional eval-equivalence; **`P = Computable`** |
| `SemanticSelfDescription/Theorems/NoSelfErasure.lean` | `no_weak_self_erasure`, `no_strong_self_erasure` | Weak and strong self-erasure ruled out |
| `SemanticSelfDescription/Theorems/SemanticRemainder.lean` | `semantic_remainder_or_nontotal` | Every internal self-theory fails totality or leaves irreducible remainder |
| `SemanticSelfDescription/Theorems/PhysicalCorollary.lean` | `no_final_internal_gut` | Physical corollary: no final internal GUT |
| `SemanticSelfDescription/Bridge/ToSelectorStrength.lean` | Bridge to Paper 29 barrier | FinalSelfTheory ⇒ total decider |
| `SemanticSelfDescription/Bridge/ToReflection.lean` | Bridge to Paper 28 | hFP from DiagClosed; **`false_of_encodedNontrivial_aligns_univ`** (aligned universal relation ⇒ no `EncodedNontrivial`) |
| `SelfReference/Minimality/UnitypedNatReprObstruction.lean` | `not_nonempty_sri0'_nat_equiv_eq` | **Unityped `ℕ`:** no `SRI₀′` with `Equiv = Eq` (Lawvere diagonal); clarifies `Code = ℕ` + `barrier_hypotheses_from_reflection` closure tension |
| `SemanticSelfDescription/Bridge/ToCertificationLogic.lean` | Bridge to Paper 50 | Necessary incompleteness implies certification boundary |

SemanticSelfDescription library: **0 sorry**, 0 custom axioms. Depends on SelectorStrength, Reflection, Learning, SelfAwareness, CertificationLogic. Build: full `lake build` from nems-lean root.

### New Targets Program (new_targets.tex, March 2026)

| Library | Theorem/Def | Statement |
|---------|-------------|-----------|
| **InternalitySchema** (Program I) | |
| `InternalitySchema/Core/SystemTask.lean` | SystemTaskInterface, Outsources | Load-bearing, internally realizable, completed by, internal to |
| `InternalitySchema/Theorems/OutsourcingBarrier.lean` | `outsourcing_barrier` | LoadBearing ∧ ¬InternallyRealizable ∧ CompletedBy ⇒ ¬InternalTo |
| `InternalitySchema/Theorems/NEMSRecovery.lean` | `nems_recovery` | Non-cat + no internal selector ⇒ any selector non-internal |
| `InternalitySchema/Theorems/Foundationality.lean` | `Foundational`, `foundational_iff_internal_completion`, `foundational_implies_no_external_selection` | **Meta-Principle 2:** Foundational ↔ ObsCategorical ∨ ∃ internal selector (Paper 82) |
| **SurvivorCalculus** (Program III) | |
| `SurvivorCalculus/Core/Cascade.lean` | Cascade, ResidualClass | Predicate cascade on base space |
| `SurvivorCalculus/Theorems/MonotoneFiltering.lean` | `residual_inclusion` | R_{k+1} ⊆ R_k |
| **AdmissibleContinuation** (Program II) | |
| `AdmissibleContinuation/Core/ContinuationSystem.lean` | ContinuationSystem, ClosureCompatible, BurdenBearing | State/update/record structure |
| `AdmissibleContinuation/Theorems/ClosureCompatibleContinuation.lean` | `closure_compatible_continuation` | ClosureCompatible ∧ BurdenBearing ⇒ AdmissibleContinuation |
| **ForcedAdjudication** (Program IV) | |
| `ForcedAdjudication/Core/AdjudicativeRole.lean` | `forced_adjudicative_role` | PSC + choice ⇒ PT exists (re-export MFRR) |
| **StructuralNonExhaustibility** (Program V) | |
| `StructuralNonExhaustibility/Core/ReflexiveSystem.lean` | ReflexiveSystem, NoTotalExhaustion | Schema for no total exhaustive internalization |
| `StructuralNonExhaustibility/Theorems/NoTotalExhaustion.lean` | `no_total_exhaustion_of` | BarrierHyp ⇒ ¬ TotalExhaustiveInternal |
| `StructuralNonExhaustibility/Theorems/InternalizationNotTotalization.lean` | `InternalizationNotTotalization`, `internalization_not_totalization` | **Meta-Principle 3:** Under barrier premises, total exhaustive internal completion fails (Paper 82) |
| `StructuralNonExhaustibility/Bridges/ToSemanticSelfDescription.lean` | Bridge to Paper 51 | no_final_self_theory instance |

**Fixes:** Sieve.Theorems.Residual: `List.forall_map` → `List.forall_map_iff` (Mathlib 4.29). Sieve added to lakefile.

## Key source files (SHA-256)

To verify integrity, compute `sha256sum` on the following files and compare:

```
NemS.lean
NemS/Prelude.lean
NemS/Core/Basics.lean
NemS/Core/ObsEq.lean
NemS/Core/Categoricity.lean
NemS/Core/Selectors.lean
NemS/Core/Trichotomy.lean
NemS/Core/Internality.lean
NemS/Reduction/Externality.lean
NemS/Reduction/EnlargedSpace.lean
NemS/Reduction/ER.lean
NemS/Visibility/Recordability.lean
NemS/Visibility/SelfEncoding.lean
NemS/Visibility/SemanticExternality.lean
NemS/Diagonal/ASR.lean
NemS/Diagonal/HaltingReduction.lean
NemS/Diagonal/Barrier.lean
NemS/Diagonal/Instantiation.lean
NemS/MFRR/ChoicePoints.lean
NemS/MFRR/PSCBundle.lean
NemS/MFRR/PTSelector.lean
NemS/MFRR/DiagonalBarrier.lean
NemS/MFRR/BridgeToNEMS.lean
NemS/MFRR/PTNonEffective.lean
NemS/MFRR/ToyMFRR.lean
NemS/ReverseBICS.lean
NemS/ReverseBICS/BICS.lean
NemS/ReverseBICS/BICS_Implies_NEMS.lean
NemS/ReverseBICS/BICS_To_PSC.lean
NemS/Adjudication/Basic.lean            # Paper 15: Choice points and Adjudicator definitions
NemS/Adjudication/NoEmulation.lean      # Paper 15: No-Emulation theorem (no emulator exists)
NemS/Adjudication/EffectiveEmulator.lean # Paper 16: Stronger no-emulation theorem via instance encoding
NemS/RelativePSC/FrameworkA.lean        # Paper 16: Subsystem framework definitions
NemS/RelativePSC/RelativeNEMS.lean      # Paper 16: Relative NEMS and Recursive NEMS theorem
NemS/RelativePSC/DiagonalHeredity.lean  # Paper 16: Heredity of the diagonal barrier
NemS/Observers/RecordStability.lean     # Paper 17: Record stability and coherence constraints
NemS/Observers/AdjudicatorNetwork.lean  # Paper 17: Adjudicator networks and weak necessity
NemS/RSMC/RSMC.lean                     # Paper 17: Reflexive Self-Model Closure (RSMC)
NemS/RSMC/AdjudicatorImpliesRSMC.lean   # Paper 17: Adjudication requires RSMC conditional
NemS/Optimality/Terminality.lean        # Paper 18: Semantic Terminality and end of reductionism
NemS/Adjudication/ExecutionNecessity.lean # Paper 19: Non-emulability of execution (Agentic Necessity)
NemS/Physics/Rigidity.lean              # Paper 20: Rigidity of the Lagrangian (Mathematical Uniqueness)
NemS/Terminality/ExistentialRigidity.lean # Paper 21: Existential Rigidity (The End of Choice)
NemS/Adjudication/IrreducibleAgency.lean  # Paper 22: Irreducible Agency (Non-Algorithmic Adjudication)
NemS/Reflexive/FinalityTheorem.lean     # Paper 23: Foundational Finality (The Master Loop)
NemS/Cosmology/SemanticFloor.lean       # Paper 24: The Theorem of the Semantic Floor
NemS/Cosmology/UnifiedClosureFramework.lean  # Paper 78: Bridge ontology
NemS/Cosmology/CosmologicalClosureSchema.lean
NemS/Cosmology/Bridges/ToSemanticFloor.lean
NemS/Cosmology/Bridges/ToArrowOfTime.lean
NemS/Cosmology/Bridges/ToFinality.lean
NemS/Cosmology/Bridges/ToFoundationalFinality.lean
NemS/Cosmology/Bridges/ToGPTClosure.lean
NemS/Cosmology/Bridges/ToLawCalibration.lean
NemS/Cosmology/Bridges/ToAdjudicators.lean
NemS/Cosmology/StrongCosmologicalClosureSchema.lean
NemS/Cosmology/CosmologicalClosureUnification.lean  # Paper 78: Grand Unification
NemS/Cosmology/FoundationalAdmissibility.lean       # Paper 79: EPIC_67_FA
NemS/Cosmology/ClassificationCascade.lean           # Paper 80: Survivor selection cascade
NemS/Cosmology/UnifiedClosureFramework/Examples/Toy.lean
NemS/Bridge/UnifiedRigidity.lean        # Paper 25: The Unified Rigidity Theorem
NemS/Examples/Toy.lean
NemS/Meta/AuditProtocol.lean
Closure.lean
Closure/Core/ObsSemantics.lean
Closure/Core/Selector.lean
Closure/Core/Internal.lean
Closure/Core/Canonicalization.lean
Closure/Core/Effective.lean
Closure/Theorems/AuditSoundness.lean
Closure/Theorems/Preservation.lean
Closure/Theorems/BoundedSelector.lean
Closure/Bridge/SelfReferenceInstance.lean
Closure/Examples/FintypeWorld.lean
SelfReference.lean
SelfReference/Core/Interface.lean
SelfReference/Core/Representability.lean
SelfReference/Core/FixedPoint.lean
SelfReference/Consequences/DiagonalBarrier.lean
SelfReference/Instances/NEMS.lean
Reflection.lean
Reflection/Core/SRI_R.lean
Reflection/Theorems/DiagonalClosure.lean
Reflection/Hierarchy/Examples.lean
Reflection/Hierarchy/Separation.lean
Reflection/Bridge/ClosureInstance.lean
SelectorStrength.lean
SelectorStrength/Core/Strength.lean
SelectorStrength/Core/Deciders.lean
SelectorStrength/Core/AntiDecider.lean
SelectorStrength/Theorems/BarrierSchema.lean
SelectorStrength/Theorems/Monotonicity.lean
SelectorStrength/Bridge/Reflection.lean
SelectorStrength/Bridge/Closure.lean
SelectorStrength/Instances/Trivial.lean
SelectorStrength/Instances/ComputableNat.lean
Learning.lean
Learning/Core/Certificates.lean
Learning/Core/SelfTrust.lean
Learning/Theorems/SelfTrustBarrier.lean
Learning/Bridge/Reflection.lean
Learning/Examples/ToyGuarantee.lean
Learning/Positive/Stratified.lean
EpistemicAgency.lean
EpistemicAgency/Core/ClaimDomain.lean
EpistemicAgency/Core/Agent.lean
EpistemicAgency/Core/Protocol.lean
EpistemicAgency/Theorems/NoSelfCertifierImported.lean
EpistemicAgency/Theorems/ProtocolStrictImprovement.lean
EpistemicAgency/Theorems/Diversity.lean
EpistemicAgency/Theorems/MetaBarrier.lean
EpistemicAgency/Examples/ToySociety.lean
SelfImprovement.lean
SelfImprovement/Core/Upgrades.lean
SelfImprovement/Theorems/Barrier.lean
SelfImprovement/Theorems/Stratified.lean
SelfImprovement/Theorems/SocietyImproves.lean
SelfImprovement/Theorems/MetaBarrier.lean
SelfImprovement/Examples/ToyUpgrades.lean
SelfAwareness.lean
SelfAwareness/Core/ClaimFamilies.lean
SelfAwareness/Core/SelfModel.lean
SelfAwareness/Theorems/Hierarchy.lean
SelfAwareness/Theorems/SelectorNecessity.lean
SelfAwareness/Theorems/IntrospectiveOptimality.lean
SelfAwareness/Examples/ToyHierarchy.lean
SelfAwareness/Examples/ToyMultiplicity.lean
SelfAwareness/Examples/ToyRightness.lean
Sieve.lean
Sieve/Core/TheorySpace.lean
Sieve/Core/Constraints.lean
Sieve/Theorems/Residual.lean
Sieve/Examples/ToyDomain.lean
Hypercomputation.lean
Hypercomputation/Core/OracleAsSelector.lean
Hypercomputation/Core/HypercomputerClaim.lean
Hypercomputation/Core/Taxonomy.lean
Hypercomputation/Theorems/NoInternalHypercomputer.lean
Hypercomputation/Theorems/OracleAudit.lean
Hypercomputation/Theorems/Taxonomy.lean
Hypercomputation/Examples/Halting.lean
Hypercomputation/Examples/RecordTruth.lean
ArrowOfTime.lean
ArrowOfTime/Core/RecordFiltration.lean
ArrowOfTime/Core/Refinement.lean
ArrowOfTime/Theorems/ArrowRefinement.lean
ArrowOfTime/Theorems/NoOverwrite.lean
ArrowOfTime/Theorems/Irreversibility.lean
ArrowOfTime/Theorems/ClosureArrow.lean
ArrowOfTime/Theorems/SelectionBarrier.lean
ArrowOfTime/Examples/Toy.lean
RefinementFlow.lean
RefinementFlow/Core/RefinementFlow.lean
RefinementFlow/Examples/ToyBits.lean
RecordEntropy.lean
RecordEntropy/Core/EntropyFinite.lean
RecordEntropy/Theorems/Monotonicity.lean
RecordEntropy/Theorems/NoncomputabilityBarrier.lean
RecordEntropy/Theorems/UniformEntropyBarrier.lean
RecordEntropy/Examples/ToyEntropy.lean
ErrorCorrectingClosure.lean
ErrorCorrectingClosure/Core/DecodingModel.lean
ErrorCorrectingClosure/Theorems/DecoderBarrier.lean
ErrorCorrectingClosure/Theorems/ProtocolImprovement.lean
ErrorCorrectingClosure/Examples/ToyDecoder.lean
LawCalibration.lean
LawCalibration/Core/LawUpdate.lean
LawCalibration/Theorems/LawFixedPoints.lean
LawCalibration/Theorems/LawSelectionBarrier.lean
LawCalibration/Examples/ToyLaw.lean
SemanticNonlocality.lean
SemanticNonlocality/Core/LocalityAxioms.lean
SemanticNonlocality/Theorems/LocalDynamicsNotLocalSemantics.lean
SemanticNonlocality/Examples/ToyFactorization.lean
CausalNonlocality.lean
CausalNonlocality/Theorems/NoGo.lean
CausalNonlocality/Examples/ToyNoGo.lean
CertificationLogic.lean
CertificationLogic/Core/InstanceSemantics.lean
CertificationLogic/Core/Protocols.lean
CertificationLogic/Core/Formulas.lean
CertificationLogic/Core/CertifiableAt.lean
CertificationLogic/Theorems/CapstoneSoundness.lean
CertificationLogic/Theorems/CapstoneCompleteness.lean
CertificationLogic/Theorems/Maximality.lean
CertificationLogic/Examples/ToyFinite.lean
CertificationLogic/Examples/ToyBoundary.lean
ChronologyUnderClosure.lean
ChronologyUnderClosure/Core/RecordDynamics.lean
ChronologyUnderClosure/Theorems/RecordNonOverwrite.lean
ChronologyUnderClosure/Theorems/SelectionBarrier.lean
BlackHoles.lean
BlackHoles/Core/RecordFragments.lean
BlackHoles/Theorems/NoHypercomputingFromBH.lean
GPTClosure.lean
GPTClosure/Core/OrderedSpaces.lean
GPTClosure/Core/EffectsStates.lean
GPTClosure/Core/Measurements.lean
GPTClosure/Theorems/Uniqueness.lean
GPTClosure/Theorems/ClosurePrinciples.lean
GPTClosure/Examples/Toy.lean
GPTClosure/Instances/QuantumFinite.lean
InstitutionalEpistemics.lean
InstitutionalEpistemics/Core/Roles.lean
InstitutionalEpistemics/Core/ThreatModel.lean
InstitutionalEpistemics/Core/Protocols.lean
InstitutionalEpistemics/Theorems/NoUniversalJudge.lean
InstitutionalEpistemics/Theorems/LowerBounds.lean
InstitutionalEpistemics/Theorems/RobustnessImprovement.lean
InstitutionalEpistemics/Examples/ToyRegulation.lean
lakefile.lean
lean-toolchain
```

## Reproduction

```bash
# From a clean checkout of this repository at tag v2.0.0:
lake update    # fetches Mathlib (cached oleans downloaded automatically)
lake build     # compiles the full library
```

Expected output: `Build completed successfully.`

## What is axiomatized vs. proved

### Core
- **Axiomatized:** `Framework` (Model, Rec, Truth); `IsInternal` predicate (abstract parameter)
- **Proved:** all implication structure (Trichotomy, ER, determinacy-PSC, semantic visibility, audit equivalence)
- **Two instantiations provided:** definability-style and computability-style internality

### Diagonal Barrier
- **Axiomatized:** nothing (zero custom axioms)
- **Proved:** ASR ⇒ record-truth not computable, via reduction to Mathlib's `ComputablePred.halting_problem`
- **Concrete instantiation:** halting framework demonstrates ASR is satisfiable

### MFRR Bridge
- **Axiomatized:** nothing (zero custom axioms)
- **Proved:** choice points ⇒ non-categoricity; PSC + choice ⇒ PT exists; PSC + choice + diagonal ⇒ constrained selection; PSC classification; no external law
- **Toy instantiation:** Bool framework with record-divergent choice, PSC bundle, and PT extraction

### Summary: the entire library has **zero custom axioms** beyond Lean's kernel axioms.

---

## General Self-Reference Calculus (v2.2.0)

### SelfReference.Core

| File | Definition/Theorem | Statement |
|------|--------------------|-----------|
| `SelfReference/Core/Interface.lean` | `SRI` typeclass | Abstract self-reference interface: `Equiv`, `quote`, `run`, `repr`, `repr_spec`, `eval_quote` |
| `SelfReference/Core/Interface.lean` | `CSRI` typeclass | SRI + `quote_cong` (congruence of quotation) |
| `SelfReference/Core/Representability.lean` | `diag` | Diagonal code: `repr (fun c => F (quote (run c c)))` |
| `SelfReference/Core/Representability.lean` | `diag_spec` | `run (diag F) c ≃ F (quote (run c c))` |
| `SelfReference/Core/Representability.lean` | `diag_code_fixed_point` | `run (diag F) (quote (diag F)) ≃ F (quote (diag F))` |
| `SelfReference/Core/FixedPoint.lean` | `CSRI.master_fixed_point` | **MFP-1**: ∀ F congruent, ∃ d, d ≃ F d |
| `SelfReference/Core/FixedPoint.lean` | `CSRI.master_fixed_point_code` | Code-level fixed point: ∃ d, run d (quote d) ≃ F (quote d) |

### SelfReference.Consequences

| File | Theorem | Statement |
|------|---------|-----------|
| `SelfReference/Consequences/DiagonalBarrier.lean` | `no_total_decider` | **MFP-2**: Extensional nontrivial T + total decider → False |
| `SelfReference/Consequences/DiagonalBarrier.lean` | `no_total_decider_nontrivial` | No extensional nontrivial predicate has a total decider |

### SelfReference.Instances

| File | Theorem | Statement |
|------|---------|-----------|
| `SelfReference/Instances/Godel.lean` | `godel_diagonal_lemma` | **Gödel diagonal lemma**: ∀ F congruent, ∃ ψ, ProvBic ψ (F ψ) |
| `SelfReference/Instances/Godel.lean` | `godel_sentence` | Gödel sentence: ∃ ψ, ProvBic ψ (neg (prov ψ)) |
| `SelfReference/Instances/Kleene.lean` | `kleene_recursion_theorem` | **Kleene recursion theorem**: ∀ F, ∃ e, ExtEq e (F e) |
| `SelfReference/Instances/Kleene.lean` | `rogers_fixed_point` | Rogers' fixed-point theorem |
| `SelfReference/Instances/NEMS.lean` | `nems_rt_no_total_bool_decider` | NEMS diagonal barrier (abstract form, 1 sorry for fixed-point step) |
| `SelfReference/Instances/Loeb.lean` | `lob` | **Löb's theorem**: T ⊢ □φ → φ implies T ⊢ φ (diagonal step proved; HBL chaining 1 sorry) |

### SelfReference.Minimality

| File | Theorem | Statement |
|------|---------|-----------|
| `SelfReference/Minimality/Countermodels.lean` | `bool_not_no_fixed_point` | `not` has no fixed point on Bool |
| `SelfReference/Minimality/Countermodels.lean` | `shift_breaks_eval_quote` | Shifting `quote` breaks `eval_quote` |
| `SelfReference/Minimality/StratifiedReflection.lean` | `stratum1_not_implies_stratum2` | Partial internalization does not imply full internalization |
| `SelfReference/Minimality/StratifiedReflection.lean` | `universal_diagonal_trichotomy` | **Universal Diagonal Trichotomy**: every system is Stratum 0, 1, or 2 |
| `SelfReference/Minimality/StratifiedReflection.lean` | `stratum2_implies_diagonal_barrier` | Stratum 2 (full SRI) implies the diagonal barrier |

### The Universal Diagonal Trichotomy

The flagship result of the SelfReference library:

> **Theorem** (`universal_diagonal_trichotomy`): For any type `α`, exactly one of:
> 1. It lacks Stratum 1 structure (no internalization — NEMS Class I).
> 2. It has Stratum 1 but not Stratum 2 (partial internalization — NEMS Class IIa).
> 3. It has Stratum 2 (full internalization — NEMS Class IIb, diagonal barrier applies).

NEMS I/IIa/IIb correspond precisely to Strata 0/1/2.

## Companion papers

This artifact formalizes the core spine of:
- *Semantic Closure Under No External Model Selection* (NEMS Theorem paper)
- *The NEMS Framework* (overview document)
- *From NEMS to MFRR: A Machine-Checked Bridge* (Paper 21)
- *General Self-Reference Calculus* (Paper 26 — the SelfReference library)
- *A No-Free-Bits Calculus for Determinacy and Outsourcing* (Paper 27 — the Closure library: audits, canonicalization, effective semantics, BoundedSelector, FintypeWorld)
- *Reflection as a Resource* (Paper 28 — the Reflection library: SRI_R, DiagClosed, Diagonal Closure Theorem, restricted_master_fixed_point, hierarchy, bridge from Closure)
- *Selector Strength and Completion Hierarchies* (Paper 29 — the SelectorStrength library: barrier schema no_total_decider_at_strength, monotonicity, bridges to Reflection/Closure, trivial and computable-Nat instances)
- *Second Incompleteness for Self-Certifying Learners* (Paper 30 — the Learning library: no_total_self_certifier, reflection_supplies_hFP_for_learning, stratified_self_certification_toy, ToyGuarantee; 0 sorry)
- *Epistemic Agency Under Diagonal Constraints* (Paper 31 — the EpistemicAgency library: society as verification protocol, strict separation, diversity necessity, meta-barrier; 0 sorry)
- *Self-Improvement Under Diagonal Constraints* (Paper 32 — SelfImprovement library; 0 sorry)
- *Self-Awareness as a Resource* (Paper 33 — SelfAwareness library; 0 sorry)
- *A Sieve Engine for Theory Spaces* (Paper 34 — the Sieve library: theory space, constraints as list, SieveHolds, Residual, monotonicity, pullback/functoriality, ToyDomain; 0 sorry)
- *Oracles as External Selectors: NEMS Constraints on Hypercomputation and Physical Computability* (Paper 35 — the Hypercomputation library: oracle-as-selector audit, no_internal_hypercomputer_at_strength, internal_hypercomputer_claim_forces_premise_failure, halting and record-truth examples; 0 sorry)
- *The Arrow of Time from Closure* (Paper 36 — ArrowOfTime library: record filtration, refinement, no_overwrite, irreversibility, selection_barrier_retrodiction, Toy; 0 sorry)
- *Chronology Under Closure: NEMS Constraints on Admissible Time Travel* (Paper 37 — ChronologyUnderClosure library: record dynamics, record_non_overwrite, selection_barrier_chronology; 0 sorry)
- *NEMS Constraints on Black Hole Information* (Paper 38 — BlackHoles library: record_consistency_abstract, no_hypercomputing_from_bh; 0 sorry)
- *Probability as Closure in General Probabilistic Theories* (Paper 39 — GPTClosure library: state_ext_effect_span, uniqueness_under_spanning, closure_implies_affine_linear, Toy; 0 sorry in core; GPTClosure/Instances/QuantumFinite bridges Paper 13 ↔ Paper 39: quantumOUS, born_rule_is_gpt_prob, povmToMeasurement, quantum_state_uniqueness; 3 sorry)
- *Institutions Under Diagonal Constraints* (Paper 40 — InstitutionalEpistemics library: no_universal_final_judge, k_role_lower_bound, diversity_necessity, ToyRegulation; 0 sorry)
- *Refinement Flow of World-Types: Time as Growth of Stable Distinguishability* (Paper 41 — RefinementFlow library: forgetFromTo, forgetFromTo_coherent, forgetFromTo_naturality, ToyBits; 0 sorry)
- *Record Entropy and Noncomputability: Monotone Semantic Complexity under Diagonal Capability* (Paper 42 — RecordEntropy library: recordEntropy, recordEntropy_monotone, recordEntropy_strict, no_total_decider_entropy, ToyEntropy; 0 sorry)
- *Adjudication as Decoding: Semantic Error-Correction under PSC Closure* (Paper 43 — ErrorCorrectingClosure library: decoderClaim, no_total_decider_decoder_claim, diversity_necessity_decoding, ToyDecoder; 0 sorry)
- *Calibration as Closure: Laws as Compression Fixed Points under No-Free-Bits* (Paper 44 — LawCalibration library: uniformLawSelectorClaim, no_total_decider_uniform_law_selector, fixed_point_multiplicity, ToyLaw; 0 sorry)
- *Local Dynamics, Global Semantics: A Closure Engine for Semantic Nonlocality* (Paper 45 — SemanticNonlocality library: LocalityAxioms, same_local_views_imp_obs_equiv, same_local_views_imp_same_world_type, ToyFactorization; 0 sorry)
- *Causal Nonlocality from Closure* (Paper 46 — CausalNonlocality library: no_local_semantic_determinacy, toy_no_go parametric in hFP; 0 sorry, 0 axioms)
- *Cosmic Audit: Universe as a Self-Auditing Institution* (Paper 49 — InstitutionalEpistemics.CosmicAudit: forced_distributed_adjudication, diversity_necessary_strict_improvement; 1 sorry in Examples.ToyCosmic)
- *A Complete Logic of Certification: Soundness, Completeness, and Maximality for Stratified Verification Protocols* (Paper 50 — CertificationLogic: soundness_capstone, completeness_capstone, boundary_maximality, protocolCoverage_subset_union_atoms, toy_equiv, toy_boundary; 0 sorry)
- *Necessary Incompleteness of Internal Semantic Self-Description* (Paper 51 — SemanticSelfDescription: no_final_self_theory, no_weak_self_erasure, no_strong_self_erasure, semantic_remainder_or_nontotal; 0 sorry)

**Papers 52–65 (reflexive-closure-lean):** The reflexive-closure arc (direct self-semantic fixed points, syntax-semantics separation, observer corollaries, qualia and the ledger, reflexive closure theorem, reflexive unfolding, necessary reflexive intelligence, calculus of intelligence, reality as recursive intelligence, ghost collapse, ledger grounding, Alpha theorem, grounded existence, qualia as Alpha-grounded content) is formalized in the sibling repo **reflexive-closure-lean**. See that repo's MANIFEST.md for theorem names and module structure. Libraries: SemanticSelfReference (52), SyntaxSemantics (53), QualiaLedger (55), ReflexiveClosure (56), ReflexiveUnfolding (57), NecessaryReflexiveIntelligence (58), CalculusOfIntelligence (59), RealityAsRecursiveIntelligence (60), GhostCollapse (61), LedgerGround (62), Alpha (63), GroundedExistence (64), QualiaAlphaGrounded (65).
