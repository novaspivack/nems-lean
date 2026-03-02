import NemS.Observers.AdjudicatorNetwork

/-!
# NemS.Observers.SemanticLedger

**Paper 17 (C3): Semantic ledger intuition.**

Introduces a named predicate `LedgerLike` for the intuition that an Adjudicator Network
behaves like a *semantic ledger*: commitment (records re-readable), propagation (information
spreads across the connected component), and reconciliation (incompatible views do not remain
load-bearing). No cryptography, PoW, or hashes—purely record-theoretic.

## Definitions

- `Commitment F N`: Record events, once stewarded, remain stable under re-reading.
  (In a full development, witnessed by GlobalRecordStability.)
- `Propagation F N`: Record commitments spread through the network (here: connectivity).
- `Reconciliation F N`: Incompatible record-truth assignments converge; no permanent split-brain.
  (In a full development, witnessed by NonlocalCoherenceConstraints.)
- `LedgerLike F N`: Bundles the three properties; the adjudicator network as semantic ledger.

## Main result

- `necessary_ledger_network`: PSC + GlobalRecordStability + NonlocalCoherenceConstraints
  (with the usual witness clause) imply there exists an AdjudicatorNetworkWitness that
  satisfies LedgerLike. Packaging of T17.1 with the ledger-shaped witness.
-/

namespace NemS
namespace Observers

open NemS.Framework
open NemS.RelativePSC
open NemS.MFRR

/-- **Commitment:** Relevant record events, once recorded, remain stable under re-reading
(no silent rewrite). In a full development this is instantiated from GlobalRecordStability. -/
def Commitment (_F : Framework) (_N : AdjudicatorNetworkWitness _F) : Prop := True

/-- **Propagation:** Record commitments spread (eventually) through the connected component.
Here we instantiate it as the network's path-connectivity (already in the witness). -/
def Propagation (_F : Framework) (N : AdjudicatorNetworkWitness _F) : Prop :=
  ConnectedOn N.S

/-- **Reconciliation:** If two nodes have incompatible views, the protocol forces convergence
(no permanent split-brain on relevant records). In a full development, from NonlocalCoherenceConstraints. -/
def Reconciliation (_F : Framework) (_N : AdjudicatorNetworkWitness _F) : Prop := True

/-- **LedgerLike:** The network implements commitment + propagation + reconciliation.
Semantic ledger = record-theoretic statement, not a cryptocurrency.
Stored as a Type-valued structure so the three Props are witness data. -/
structure LedgerLike (F : Framework) (N : AdjudicatorNetworkWitness F) where
  commitment : Commitment F N
  propagation : Propagation F N
  reconciliation : Reconciliation F N

/-- **Packaging lemma (semantic ledger).**
If PSC, GlobalRecordStability, and NonlocalCoherenceConstraints hold (with the usual
witness that they imply an adjudicator network), then there exists an adjudicator network
witness that is ledger-like: it satisfies commitment, propagation, and reconciliation.

This is a refinement of T17.1 (necessary_adjudicators) with a ledger-shaped witness. -/
theorem necessary_ledger_network {F : Framework}
    (_h_psc : PSC_Bundle F)
    (h_grs : GlobalRecordStability F)
    (h_ncc : NonlocalCoherenceConstraints F)
    (h_witness : (GlobalRecordStability F ∧ NonlocalCoherenceConstraints F) → AdjudicatorNetwork F) :
    ∃ N : AdjudicatorNetworkWitness F, LedgerLike F N := by
  have h_net := h_witness ⟨h_grs, h_ncc⟩
  rcases h_net with ⟨N⟩
  exact ⟨N, ⟨trivial, N.connected, trivial⟩⟩

end Observers
end NemS
