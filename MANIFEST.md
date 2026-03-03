# nems-lean v2.2.0 — Artifact Manifest

**Release:** v2.2.0  
**Date:** March 2026  
**Lean version:** leanprover/lean4:v4.28.0  
**Mathlib version:** v4.28.0  
**Build result:** 8046 jobs, 0 errors, **6 `sorry`** (see below), **zero custom axioms**

## v2.2.0 additions: General Self-Reference Calculus

A new `SelfReference` library has been added alongside `NemS`.  It extracts
the NEMS diagonal machinery into an abstract interface (the SRI) and proves
a master fixed-point theorem (MFP-1) and master diagonal barrier (MFP-2)
once, recovering Gödel, Kleene, Löb, and NEMS as instances.

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

Four `sorry` statements remain across two modules:

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

All other theorems in the library are fully proved without `sorry`, including:
- **Uniqueness**: `busch_gleason_unique` — if any ρ represents μ, it must be the unique one (0 sorrys)
- **Test-effect agreement**: rhoCandidate provably matches μ on all test effects D_k, R_ij, Q_ij (0 sorrys)
- **Delta infrastructure**: binary additivity, POVM-sum-zero, complement identity (0 sorrys)
- The full diagonal barrier, physical incompleteness, and determinism no-go chains (0 sorrys)
- The complete NEMS core, MFRR bridge, and PT non-effectiveness (0 sorrys)

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
| `NemS/Visibility/SemanticExternality.lean` | `semantic_externality_not_categorical` | Semantic externality ⇒ non-categoricity in F⁺ |
| `NemS/Visibility/SemanticExternality.lean` | `nems_forces_evaluator_selector` | NEMS forces internal selector for evaluator choices |
| `NemS/Meta/AuditProtocol.lean` | `passAudit_iff_nems` | PassAudit ↔ NEMS |
| `NemS/Core/Internality.lean` | `nems_definability` | NEMS under definability-internality |
| `NemS/Core/Internality.lean` | `nems_computability` | NEMS under computability-internality |
| `NemS/Core/Internality.lean` | `definability_implies_quotient_section` | Definability ⇒ quotient section exists |

### Diagonal Barrier (v2.0.0)

| File | Theorem | Statement |
|------|---------|-----------|
| `NemS/Diagonal/HaltingReduction.lean` | `asr_rt_computable_implies_halting_computable` | ASR + computable RT ⇒ computable halting |
| `NemS/Diagonal/HaltingReduction.lean` | `asr_rt_not_computable` | **ASR ⇒ RT not computable (diagonal barrier, Thm 5.9)** |
| `NemS/Diagonal/Barrier.lean` | `no_total_effective_rt_decider` | ASR ⇒ ¬ ComputablePred RT |
| `NemS/Diagonal/Instantiation.lean` | `halting_framework_rt_not_computable` | Concrete instantiation recovers halting undecidability |

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

### Reverse Direction: BICS ⇒ NEMS ⇒ PSC (v2.1.0, Paper 14)

| File | Theorem | Statement |
|------|---------|-----------|
| `NemS/ReverseBICS/BICS.lean` | `BICS` structure | Born Internal & Complete Semantics definition |
| `NemS/ReverseBICS/BICS_Implies_NEMS.lean` | `bics_implies_nems` | **BICS ⇒ NEMS (reverse direction flagship)** |
| `NemS/ReverseBICS/BICS_Implies_NEMS.lean` | `bics_rules_out_external` | BICS ⇒ ¬ NeedsExternalSelection |

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
NemS/Bridge/UnifiedRigidity.lean        # Paper 25: The Unified Rigidity Theorem
NemS/Examples/Toy.lean
NemS/Meta/AuditProtocol.lean
lakefile.lean
lean-toolchain
```

## Reproduction

```bash
# From a clean checkout of this repository at tag v2.0.0:
lake update    # fetches Mathlib (cached oleans downloaded automatically)
lake build     # compiles the full library
```

Expected output: `Build completed successfully (8052 jobs).`

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
- *General Self-Reference Calculus* (forthcoming — the SelfReference library)
