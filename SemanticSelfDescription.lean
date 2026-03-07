import SemanticSelfDescription.Core.Claims
import SemanticSelfDescription.Core.SelfTheory
import SemanticSelfDescription.Core.SelfScope
import SemanticSelfDescription.Core.SelfErasure
import SemanticSelfDescription.Bridge.ToSelectorStrength
import SemanticSelfDescription.Bridge.ToReflection
import SemanticSelfDescription.Bridge.ToLearning
import SemanticSelfDescription.Bridge.ToSelfAwareness
import SemanticSelfDescription.Bridge.ToCertificationLogic
import SemanticSelfDescription.Theorems.NoFinalSelfTheory
import SemanticSelfDescription.Theorems.NoSelfErasure
import SemanticSelfDescription.Theorems.SemanticRemainder
import SemanticSelfDescription.Theorems.PhysicalCorollary

/-!
# SemanticSelfDescription — Necessary Incompleteness of Internal Semantic Self-Description

No sufficiently expressive realized universe can internally contain a final,
faithful, complete theory of its own realized semantics.

This library formalizes the theorem that the universe cannot contain a total
faithful internal GUT of its own realized semantics — stronger than ordinary
incompleteness or "no total decider." It is about internal semantic self-capture
at the world level.

## Key theorems

- `no_final_self_theory` — no final internal self-theory
- `no_weak_self_erasure` — no weak self-erasing theory
- `no_strong_self_erasure` — no strong self-erasing theory

## Module structure

- `Core.Claims` — SelfSemanticFrame, self-semantic truth
- `Core.SelfTheory` — InternalSelfTheory, FinalSelfTheory
- `Core.SelfScope` — SelfScoped, StronglySelfScoped
- `Core.SelfErasure` — WeakSelfErasing, StrongSelfErasing, SemanticClosureByTheory
- `Bridge.ToSelectorStrength` — reduction to barrier
- `Bridge.ToReflection` — DiagClosed supplies BarrierHypotheses
- `Bridge.ToLearning` — no total self-certifier (Paper 30)
- `Bridge.ToSelfAwareness` — selector necessity (Paper 33)
- `Bridge.ToCertificationLogic` — certification boundary (Paper 50)
- `Theorems.NoFinalSelfTheory` — flagship theorem
- `Theorems.NoSelfErasure` — weak and strong no-self-erasure
- `Theorems.SemanticRemainder` — positive remainder theorem
-/
