import NemS.Core.Basics
import NemS.Core.ObsEq
import NemS.Core.Categoricity
import NemS.Core.Selectors
import Closure.Core.ObsSemantics
import ArrowOfTime.Core.RecordFiltration
import NemS.Cosmology.SemanticFloor

/-!
# NemS.Cosmology.UnifiedClosureFramework

**Bridge ontology for the grand unification theorem (Paper 78).**

A single structure that can be interpreted in three ways:
1. As CosmologicalFramework (Semantic Floor)
2. As RecordFiltration (ArrowOfTime)
3. As NemS.Framework (NEMS/MFRR closure, no external law)

This is a bridge ontology, not "the final ontology of reality." It exists so one
universe can be read in three ways. No conclusion-shaped predicates (semantic floor,
irreversibility, no external runner, etc.) appear in the structure.
-/

set_option autoImplicit false

namespace NemS
namespace Cosmology

universe u v w

/-- **Unified Closure Framework.**

Minimal primitive data needed to interpret all three theorem stacks:
- CosmologicalFramework (initial boundary, semantic floor)
- RecordFiltration (stage semantics, arrow of time)
- NemS.Framework (PSC, NEMS, no external selection)

Do not add: semantic floor, irreversibility, no external runner, or any conclusion.
-/
structure UnifiedClosureFramework where
  /-- Worlds/models/realizations. -/
  World : Type u
  /-- Records/observational propositions. -/
  Rec : Type v
  /-- Truth: which records hold in which world. -/
  Truth : World → Rec → Prop
  /-- Initial state type (cosmological boundary). -/
  InitState : Type w
  /-- The initial state. -/
  init : InitState
  /-- Visible t r: record r is observable at stage t. -/
  Visible : Nat → Rec → Prop
  /-- Monotonicity: later stages see at least as much. -/
  visible_mono : ∀ t t' (r : Rec), t ≤ t' → Visible t r → Visible t' r

namespace UnifiedClosureFramework

variable (U : UnifiedClosureFramework)

/-- Time = Nat (stage index). -/
abbrev Time : Type := Nat

-- ========== Interpretation 1: NemS.Framework ==========

/-- Project to NemS.Framework for NEMS/MFRR theorems. -/
def toFramework : NemS.Framework where
  Model := U.World
  Rec := U.Rec
  Truth := U.Truth

/-- Alias for spec: project to NemS Framework. -/
def toNemSFramework : NemS.Framework := U.toFramework

instance : Coe UnifiedClosureFramework NemS.Framework where
  coe := UnifiedClosureFramework.toFramework

-- ========== Interpretation 2: CosmologicalFramework ==========

/-- Project to CosmologicalFramework for Semantic Floor theorems. -/
def toCosmologicalFramework : CosmologicalFramework where
  toFramework := U.toFramework
  InitState := U.InitState
  init := U.init

-- ========== Interpretation 3: RecordFiltration ==========

/-- Project to ArrowOfTime RecordFiltration.

RecordFiltration extends Closure.ObsSemantics; we supply Holds := Truth. -/
def toRecordFiltration : ArrowOfTime.RecordFiltration U.World U.Rec where
  Holds := U.Truth
  Visible := U.Visible
  mono := U.visible_mono

end UnifiedClosureFramework
end Cosmology
end NemS
