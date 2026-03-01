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

-- Physical universal computation → ASR
import NemS.Physical.UniversalComputation
import NemS.Physical.ASRFromUCT
import NemS.Physical.Instantiation

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
