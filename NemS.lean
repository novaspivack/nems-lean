/-!
# NemS — No External Model Selection: Lean 4 Formalization

Root barrel file. Importing this file imports the entire NEMS library.

## Module structure

- `NemS.Core`       — Framework, observational equivalence, categoricity,
                       selectors, and the Trichotomy theorem.
- `NemS.Reduction`  — External dependencies, enlarged realization space,
                       and Externality Reduction (ER).
- `NemS.Visibility` — Recordability, self-encoding extension, and semantic
                       externality reduction.
- `NemS.Diagonal`   — ASR, halting reduction, and the diagonal barrier
                       (Theorem 5.9 — fully proved, zero axioms).
- `NemS.Examples`   — Toy instantiations demonstrating the framework.
- `NemS.Meta`       — The NEMS Audit Protocol as a formal definition.
-/

import NemS.Prelude

-- Core
import NemS.Core.Basics
import NemS.Core.ObsEq
import NemS.Core.Categoricity
import NemS.Core.Selectors
import NemS.Core.Trichotomy
import NemS.Core.Internality

-- Reduction
import NemS.Reduction.Externality
import NemS.Reduction.EnlargedSpace
import NemS.Reduction.ER

-- Visibility
import NemS.Visibility.Recordability
import NemS.Visibility.SelfEncoding
import NemS.Visibility.SemanticExternality

-- Diagonal barrier (halting reduction)
import NemS.Diagonal.ASR
import NemS.Diagonal.HaltingReduction
import NemS.Diagonal.Barrier
import NemS.Diagonal.Instantiation

-- Physical universal computation → ASR → determinism no-go
import NemS.Physical.UniversalComputation
import NemS.Physical.ASRFromUCT
import NemS.Physical.Instantiation
import NemS.Physical.DeterminismNoGo

-- Quantum: Born rule from PSC
import NemS.Quantum.MatrixBasics
import NemS.Quantum.Effects
import NemS.Quantum.POVM
import NemS.Quantum.Measures
import NemS.Quantum.BuschGleason
import NemS.Quantum.BornFromPSC

-- Examples
import NemS.Examples.Toy

-- Meta
import NemS.Meta.AuditProtocol

-- MFRR Bridge
import NemS.MFRR.ChoicePoints
import NemS.MFRR.PSCBundle
import NemS.MFRR.PTSelector
import NemS.MFRR.DiagonalBarrier
import NemS.MFRR.BridgeToNEMS
import NemS.MFRR.PTNonEffective
import NemS.MFRR.ToyMFRR

-- Paper 15: No-Emulation / Self-Necessitating Adjudication
import NemS.Adjudication

-- Paper 16: Relative PSC and Recursive NEMS
import NemS.Adjudication.EffectiveEmulator
import NemS.RelativePSC

-- Paper 17: Necessary Adjudicators and RSMC
import NemS.Observers
import NemS.RSMC

-- Paper 18: The Theorem of Semantic Terminality
import NemS.Optimality

-- Paper 19: The Non-Emulability of Execution
import NemS.Adjudication.ExecutionNecessity

-- Paper 20: The Rigidity of the Lagrangian
import NemS.Physics.Rigidity

-- Paper 21: The Theorem of Existential Rigidity
import NemS.Terminality.ExistentialRigidity

-- Paper 22: Irreducible Agency (Non-Algorithmic Adjudication)
import NemS.Adjudication.IrreducibleAgency

-- Paper 23: Foundational Finality (The Master Loop)
import NemS.Reflexive.FinalityTheorem

-- Paper 24: The Theorem of the Semantic Floor
import NemS.Cosmology.SemanticFloor

-- Paper 25: The Unified Rigidity Theorem
import NemS.Bridge.UnifiedRigidity
