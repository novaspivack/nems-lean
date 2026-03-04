# nems-lean (Papers 39–40)

Lean 4 libraries for the NEMS suite.

- **Build (with network):** From this directory run `lake update` then `lake build` (builds both libraries).
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
