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

-- Reduction
import NemS.Reduction.Externality
import NemS.Reduction.EnlargedSpace
import NemS.Reduction.ER

-- Visibility
import NemS.Visibility.Recordability
import NemS.Visibility.SelfEncoding
import NemS.Visibility.SemanticExternality

-- Examples
import NemS.Examples.Toy

-- Meta
import NemS.Meta.AuditProtocol
