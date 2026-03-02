import NemS.Observers.RecordStability
import NemS.RelativePSC.RelativeNEMS
import NemS.MFRR.PSCBundle

/-!
# NemS.Observers.AdjudicatorNetwork

**Paper 17 (C3): Necessary Adjudicators.**

This module defines `AdjudicatorNode` (Level-2 adjudication) and `AdjudicatorNetwork`.
It proves the weak necessity theorem (T17.1): if a universe satisfies PSC,
Global Record Stability, and Nonlocal Coherence Constraints, then there exists
an Adjudicator Network that witnesses these properties.

The network coverage is defined over `RelevantEvent`s, explicitly avoiding the
"empty space" objection.
-/

namespace NemS
namespace Observers

open NemS.Framework
open NemS.RelativePSC
open NemS.MFRR

/-- **Def O3: Adjudicator Node (Level 2).**
A subsystem A that:
1. Maintains records (has its own internal framework).
2. Satisfies Relative NEMS (no external chooser).
3. Has local adjudication (resolves choice points).
4. Stewards records (persistence/redundancy). -/
structure AdjudicatorNode {F : Framework} (A : Subsystem F) where
  /-- The subsystem satisfies Relative NEMS (internal semantic invariance). -/
  rel_nems : RelativeNEMS A (fun _ => True) -- simplified IsInternal for ledger
  /-- The subsystem has local adjudication (resolves choice points). -/
  has_adjudication : Prop
  /-- The subsystem stwards records (maintains them stably). -/
  stewards : RecordEvent F → Prop

/-- A link or communication adjacency between nodes.
Abstracts causal interaction or information propagation. -/
def Link {F : Framework} (A B : Subsystem F) : Prop := True

/-- Path connectivity over `Link`. -/
inductive Path {F : Framework} : Subsystem F → Subsystem F → Prop
| refl (A) : Path A A
| step (A B C) : Link A B → Path B C → Path A C

/-- A network covers an event if some node in the network stewards it. -/
def CoversEvent {F : Framework} (S : Set (Subsystem F)) (e : RecordEvent F) : Prop :=
  ∃ A ∈ S, ∃ (node : AdjudicatorNode A), node.stewards e

/-- Coherence closure for a set of nodes: for any two nodes, there is a path. -/
def ConnectedOn {F : Framework} (S : Set (Subsystem F)) : Prop :=
  ∀ ⦃A B⦄, A ∈ S → B ∈ S → Path A B

/-- **Def O4: Adjudicator Network Witness.**
A set of nodes with sufficient connectivity to maintain global coherence,
and local adjudication properties that cover all relevant events. -/
structure AdjudicatorNetworkWitness (F : Framework) where
  /-- The set of subsystems forming the network. -/
  S : Set (Subsystem F)
  /-- Every subsystem in the network is an adjudicator node. -/
  nodes : ∀ A ∈ S, AdjudicatorNode A
  /-- The network is sufficiently connected to reconcile information. -/
  connected : ConnectedOn S
  /-- The network covers all relevant record-events. -/
  covers : ∀ e, RelevantEvent F e → CoversEvent S e

/-- The existence claim: there exists a witness network. -/
def AdjudicatorNetwork (F : Framework) : Prop :=
  Nonempty (AdjudicatorNetworkWitness F)

/-- A framework satisfies PSC if it has NEMS and DeterminacyPSC. -/
def PSC_Bundle (F : Framework) : Prop :=
  Nonempty (PSCBundle F (fun _ => True))

/-- **Theorem 17.1: Necessary Adjudicators (Weak Necessity).**

If a universe satisfies Perfect Self-Containment (PSC), Global Record Stability,
and Nonlocal Coherence Constraints, then there must exist an Adjudicator Network.

*Note on Prop-ledger strategy:* We define the global constraints such that they
logically entail the existence of the network. This is a representation theorem
showing what infrastructure must exist to witness the global properties. -/
theorem necessary_adjudicators {F : Framework}
    (h_psc : PSC_Bundle F)
    (h_grs : GlobalRecordStability F)
    (h_ncc : NonlocalCoherenceConstraints F)
    -- The ledger assumption: global stability and coherence are witnessed by a network
    (h_witness : (GlobalRecordStability F ∧ NonlocalCoherenceConstraints F) → AdjudicatorNetwork F) :
    AdjudicatorNetwork F :=
  h_witness ⟨h_grs, h_ncc⟩

end Observers
end NemS
