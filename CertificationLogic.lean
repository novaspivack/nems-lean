import CertificationLogic.Core.Judgment
import CertificationLogic.Theorems.Soundness
import CertificationLogic.Theorems.Completeness
import CertificationLogic.Examples.ToyLogic
import CertificationLogic.Core.InstanceSemantics
import CertificationLogic.Core.Protocols
import CertificationLogic.Core.Formulas
import CertificationLogic.Core.CertifiableAt
import CertificationLogic.Theorems.CapstoneSoundness
import CertificationLogic.Theorems.CapstoneCompleteness
import CertificationLogic.Theorems.Maximality
import CertificationLogic.Examples.ToyFinite
import CertificationLogic.Examples.ToyBoundary

/-!
# CertificationLogic — Paper 50 (Capstone)

A Complete Logic of Certification: Soundness, Completeness, and Maximality for Stratified
Verification Protocols.

**Capstone:** CertifiableAt = existence of admissible protocol witness (nontrivial semantics).
Proof system mirrors protocol combinators (atom, union, subset, stratum monotonicity).
T50.1 Soundness (protocol extraction); T50.2 Completeness (via protocol normal form);
T50.3 Maximality/boundary (SelectorStrength barrier: no extension to universal truth).
Fin 4 toy (full equivalence); Nat boundary toy (parametric in hFP). 0 axioms.
-/
