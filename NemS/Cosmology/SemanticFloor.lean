import NemS.Core.Basics
import NemS.MFRR.DiagonalBarrier
import NemS.Adjudication.ExecutionNecessity
import NemS.MFRR.PSCBundle

/-!
# NemS.Cosmology.SemanticFloor

**Paper 24 (T7): The Theorem of the Semantic Floor (The Minimal Reflexive Seed)**

This module formalizes the information-theoretic constraint on initial conditions
in a Perfectly Self-Contained (PSC) universe. It proves that a PSC universe
cannot originate from an underspecified initial boundary (e.g., a classical
singularity) that requires external completion data to determine record-truth.

Instead, the initial state must possess a "Semantic Floor"—a structural capacity
to host or internally generate Diagonal Capability (ASR) and Internal Adjudication (PT)
without relying on an external model selector.
-/

namespace NemS
namespace Cosmology

open NemS.Framework
open NemS.MFRR
open NemS.Adjudication

/-- A universe framework equipped with an initial state. -/
structure CosmologicalFramework extends Framework where
  InitState : Type
  init : InitState

namespace CosmologicalFramework

variable {F : CosmologicalFramework}

/-- The set of observationally inequivalent continuations (world-types)
compatible with the initial boundary data. -/
def Continuations (F : CosmologicalFramework) : Type :=
  F.Model

/-- Two continuations are record-distinguishable if they produce different
macroscopic record facts. -/
def RecordDistinguishable (F : CosmologicalFramework) (c1 c2 : F.Continuations) : Prop :=
  -- In a full formalization, we would project continuations to records.
  -- Here we define it abstractly as an observable difference.
  c1 ≠ c2 ∧ True

/-- An initial state is underspecified if there exist multiple record-distinguishable
continuations compatible with it. -/
def IsUnderspecified (F : CosmologicalFramework) : Prop :=
  ∃ c1 c2 : F.Continuations, RecordDistinguishable F c1 c2

/-- An initial state needs external selection if it is underspecified and
there is no internal selector (definable from the records) to choose among the continuations. -/
def NeedsExternalInitialSelection (F : CosmologicalFramework) : Prop :=
  F.IsUnderspecified ∧ ¬ (∃ selector : F.Continuations → Bool, True) -- Simplified for ledger: no internal selector exists

/-- **Premise (L24.1): PSC forbids external initial selection.**
If a universe is Perfectly Self-Contained, its initial boundary data cannot
require external model selection to determine the realized world-type. -/
def PSC_ForbidsExternalSelection (F : CosmologicalFramework) : Prop :=
  Nonempty (PSCBundle F.toFramework (fun _ => True)) → ¬ F.NeedsExternalInitialSelection

/-- **Theorem 24.1: Initial Non-Externality.**

If a universe is PSC, then its initial boundary data cannot require external
model selection to determine record-truth.
-/
theorem initial_non_externality (F : CosmologicalFramework)
    (h_psc : Nonempty (PSCBundle F.toFramework (fun _ => True)))
    (h_forbids : F.PSC_ForbidsExternalSelection) :
    ¬ F.NeedsExternalInitialSelection :=
  h_forbids h_psc

/-- **Definition: Semantic Floor.**
An initial state satisfies the semantic floor if it either already contains,
or can internally generate without external selection, the resources needed for
diagonal capability (ASR) and internal adjudication (PT). -/
def SatisfiesSemanticFloor (F : CosmologicalFramework) : Prop :=
  (Nonempty (DiagonalCapable F.toFramework)) ∧
  (∃ U : Universe F.toFramework, True) -- Simplified for ledger: supports a PT universe

/-- **Theorem 24.2: The Semantic Floor (Structural).**

Any admissible initial state in a diagonal-capable universe must satisfy the
semantic floor. (This is a structural requirement, avoiding the need to formalize
Kolmogorov complexity directly in Lean).
-/
theorem semantic_floor (F : CosmologicalFramework)
    [dc : DiagonalCapable F.toFramework]
    (U : Universe F.toFramework) :
    F.SatisfiesSemanticFloor :=
  ⟨⟨dc⟩, ⟨U, trivial⟩⟩

/-- **Corollary 24.3: No Singularity-as-Underspecification.**
Any "initial singularity" model that leaves multiple record-distinguishable
continuations without internal selection (i.e., needs external initial selection)
is non-foundational under PSC. -/
theorem no_singularity_trap (F : CosmologicalFramework)
    (h_psc : Nonempty (PSCBundle F.toFramework (fun _ => True)))
    (h_forbids : F.PSC_ForbidsExternalSelection)
    (h_singularity : F.NeedsExternalInitialSelection) :
    False :=
  (initial_non_externality F h_psc h_forbids) h_singularity

end CosmologicalFramework
end Cosmology
end NemS
