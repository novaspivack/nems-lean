/-!
# Learning — Learning and Self-Trust Incompleteness (Paper 30)

Root barrel for the Learning library (Paper 30).

This library formalizes self-trust / self-certification as an internal decider
problem and applies the strength-barrier schema (Paper 29) to obtain a
"no total internal self-certifier" theorem. It composes:

- **SelectorStrength** (Paper 29): barrier at strength S, anti-decider closure
- **Reflection** (Paper 28): supplies fixed-point premise when R is diagonally closed

## Main theorem

`Learning.Theorems.SelfTrustBarrier.no_total_self_certifier`: under extensional
nontrivial Claim, anti-decider closure, and hFP, no total internal verifier
exists at that strength.
-/

import Learning.Core.Certificates
import Learning.Core.SelfTrust
import Learning.Theorems.SelfTrustBarrier
import Learning.Bridge.Reflection
import Learning.Examples.ToyGuarantee
import Learning.Positive.Stratified
