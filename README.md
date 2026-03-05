# nems-lean (Papers 39–50)

Lean 4 libraries for the NEMS suite.

- **Build (with network):** From this directory run `lake update` then `lake build` (builds all libraries). **Do not** build a single library in isolation (e.g. `lake build CertificationLogic`) — see CertificationLogic (Paper 50) below.
- **Merge:** These files can be copied into the main `nems-lean` repository.
- **Dependencies:** Mathlib v4.29.0-rc3 (match `lean_toolchain` to your mathlib branch).

## GPTClosure (Paper 39)

- `GPTClosure.Core.OrderedSpaces` — ordered unit space, cone predicate
- `GPTClosure.Core.EffectsStates` — effects, states, `prob`
- `GPTClosure.Core.Measurements` — measurements as unit decompositions
- `GPTClosure.Theorems.Uniqueness` — `state_ext_effect_span`, `uniqueness_under_spanning`
- `GPTClosure.Theorems.ClosurePrinciples` — `ClosureAssignment`, `closure_implies_affine_linear`
- `GPTClosure.Examples.Toy` — classical simplex, `closure_axioms_hold`
- `GPTClosure.Instances.QuantumFinite` — **Paper 13 ↔ Paper 39 bridge**: `quantumCone`, `quantumOUS` (PSD cone as ordered unit space), `bornMap`, `densityToState`, `quantumEffectToGPT`, `born_rule_is_gpt_prob` (Born rule = GPT pairing), `povmToMeasurement`, `quantum_state_uniqueness`; 3 documented sorrys (PSD cone pointedness, Born-rule nonnegativity, wiring to `busch_gleason_unique`); uses explicit `@` notation to work around Lean 4.29 instance search limitation

## InstitutionalEpistemics (Paper 40)

- `InstitutionalEpistemics.Core.Roles` — roles, diversity
- `InstitutionalEpistemics.Core.ThreatModel` — instance space, adversary
- `InstitutionalEpistemics.Core.Protocols` — protocols, admissibility
- `InstitutionalEpistemics.Theorems.NoUniversalJudge` — `no_universal_final_judge` (under `DiagBarrier`)
- `InstitutionalEpistemics.Theorems.LowerBounds` — `k_role_lower_bound` (one `sorry` for pigeonhole step)
- `InstitutionalEpistemics.Theorems.RobustnessImprovement` — `diversity_necessity`
- `InstitutionalEpistemics.Examples.ToyRegulation` — toy k-partition witness

## LawCalibration (Paper 44)

- `LawCalibration.Core.LawUpdate` — Law, lawUpdate, IsFixedPoint, IsMinimalFixedPoint; LawCode, lawSelectorClaim (toy); InstanceIndex, LawInstanceCode, isMinimalForInstance, uniformLawSelectorClaim
- `LawCalibration.Theorems.LawFixedPoints` — all_fixed, fixed_point_exists, fixed_point_multiplicity, minimal_fixed_point
- `LawCalibration.Theorems.LawSelectionBarrier` — uniformLawSelectorClaim_extensional, uniformLawSelectorClaim_nontrivial, no_total_decider_uniform_law_selector
- `LawCalibration.Examples.ToyLaw` — toy_fixed_point_multiplicity, toy_lawSelectorClaim_nontrivial, toy_no_total_decider_uniform_law_selector

## SemanticNonlocality (Paper 45)

- `SemanticNonlocality.Core.LocalityAxioms` — LocalityAxioms (Fragment, LocalWorld, restrict, localHolds, factorized), same_local_views_imp_obs_equiv
- `SemanticNonlocality.Theorems.LocalDynamicsNotLocalSemantics` — same_local_views_imp_same_world_type
- `SemanticNonlocality.Examples.ToyFactorization` — toySemantics, toyLocality, toy_same_views_obs_equiv

## CausalNonlocality (Paper 46)

- `CausalNonlocality.Theorems.NoGo` — no_local_semantic_determinacy (no-go for local semantic determinacy under barrier)
- `CausalNonlocality.Examples.ToyNoGo` — ToyT, toy_no_go (parametric in hFP; 0 axioms; instantiate from Reflection/Partrec)

## CertificationLogic (Paper 50)

Stratified certification logics (protocols, formulas, certifiable-at, soundness/completeness). Uses `InstitutionalEpistemics.Core.Roles`.

**Build:** CertificationLogic must be built as part of the full project. Run `lake build` from the nems-lean root. **Do not** run `lake build CertificationLogic` alone — it can fail with cross-library resolution errors for `InstitutionalEpistemics.Role`. See **NEMS_PAPERS/NEMS_LEAN_BUILD_NOTE.md** for details.
