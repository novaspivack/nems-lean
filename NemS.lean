-- # NemS — No External Model Selection: Lean 4 Formalization
--
-- Root barrel file. Importing this file imports the entire NEMS library.
--
-- ## Module structure
--
-- - `NemS.Core`       — Framework, observational equivalence, categoricity,
-- selectors, and the Trichotomy theorem.
-- - `NemS.Reduction`  — External dependencies, enlarged realization space,
-- and Externality Reduction (ER).
-- - `NemS.Visibility` — Recordability, self-encoding extension, and semantic
-- externality reduction.
-- - `NemS.Diagonal`   — ASR, halting reduction, and the diagonal barrier
-- (Theorem 5.9 — fully proved, zero axioms).
-- - `NemS.Examples`   — Toy instantiations demonstrating the framework.
-- - `NemS.Meta`       — The NEMS Audit Protocol as a formal definition.
import NemS.Prelude
import NemS.Core.Basics
import NemS.Core.ObsEq
import NemS.Core.Categoricity
import NemS.Core.Selectors
import NemS.Core.SelectorQuotient
import NemS.Core.Trichotomy
import NemS.Core.Internality
import NemS.Core.QuotientSection
import NemS.Reduction.Externality
import NemS.Reduction.EnlargedSpace
import NemS.Reduction.ER
import NemS.Visibility.Recordability
import NemS.Visibility.SelfEncoding
import NemS.Visibility.SemanticExternality
import NemS.Diagonal.ASR
import NemS.Diagonal.HaltingReduction
import NemS.Diagonal.Barrier
import NemS.Diagonal.Instantiation
import NemS.Physical.UniversalComputation
import NemS.Physical.ASRFromUCT
import NemS.Physical.Instantiation
import NemS.Physical.DeterminismNoGo
import NemS.Quantum.MatrixBasics
import NemS.Quantum.Effects
import NemS.Quantum.POVM
import NemS.Quantum.Measures
import NemS.Quantum.BuschGleason
import NemS.Quantum.BornFromPSC
import NemS.Examples.Toy
import NemS.Meta.AuditProtocol
import NemS.MFRR.ChoicePoints
import NemS.MFRR.PSCBundle
import NemS.MFRR.PTSelector
import NemS.MFRR.DiagonalBarrier
import NemS.MFRR.BridgeToNEMS
import NemS.MFRR.PTNonEffective
import NemS.MFRR.ToyMFRR
import NemS.Adjudication
import NemS.Adjudication.EffectiveEmulator
import NemS.RelativePSC
import NemS.Observers
import NemS.RSMC
import NemS.Optimality
import NemS.Adjudication.ExecutionNecessity
import NemS.Physics.Rigidity
import NemS.Terminality.ExistentialRigidity
import NemS.Adjudication.IrreducibleAgency
import NemS.Reflexive.FinalityTheorem
import NemS.Category.PSCSys
import NemS.Category.FPSC
import NemS.Cosmology.SemanticFloor
import NemS.Cosmology.CosmologicalClosureUnification
import NemS.Cosmology.FoundationalAdmissibility
import NemS.Cosmology.ClassificationCascade
import NemS.Bridge.UnifiedRigidity
import SelfReference

-- Core
-- Reduction
-- Visibility
-- Diagonal barrier (halting reduction)
-- Physical universal computation → ASR → determinism no-go
-- Quantum: Born rule from PSC
-- Examples
-- Meta
-- MFRR Bridge
-- Paper 15: No-Emulation / Self-Necessitating Adjudication
-- Paper 16: Relative PSC and Recursive NEMS
-- Paper 17: Necessary Adjudicators and RSMC
-- Paper 18: The Theorem of Semantic Terminality
-- Paper 19: The Non-Emulability of Execution
-- Paper 20: The Rigidity of the Lagrangian
-- Paper 21: The Theorem of Existential Rigidity
-- Paper 22: Irreducible Agency (Non-Algorithmic Adjudication)
-- Paper 23: Foundational Finality (The Master Loop)
-- Paper 24: The Theorem of the Semantic Floor
-- Paper 78: Cosmological Closure Unification (Grand Unification)
-- Foundational Admissibility (viability classification)
-- Paper 80: Classification Cascade (survivor selection)
-- Paper 25: The Unified Rigidity Theorem
-- General Self-Reference Calculus (NEMS as seed crystal)
