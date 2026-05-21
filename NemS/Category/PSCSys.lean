import NemS.Optimality
import Mathlib.CategoryTheory.Category.Basic

namespace NemS.Category

open CategoryTheory NemS.Optimality

/-!
# NemS.Category.PSCSys

**C1 Final Coalgebra — Stage 1 (CatAD)**

The category **PSC-Sys** of PSC-consistent arithmetic substrates. This is the ambient
category in which `F_PSC` is an endofunctor and GTE is the terminal object (= final
`F_PSC`-coalgebra, Conjecture C1 of Paper 34).

## Thin-category construction

PSCSys is a **thin category** (preorder category). The morphisms `A → B` are proofs
that `A.T` and `B.T` are record-equivalent in the shared PSC-compatible theory space.

- **Identity** = reflexivity of record equivalence.
- **Composition** = transitivity of record equivalence.
- **Associativity / unit laws** hold by proof irrelevance (`Subsingleton.elim`),
  since `Hom A B := PLift (S.RecordEquivalent A.T B.T)` is a subsingleton type.

## Terminal object = GTE

In a thin category, terminal = greatest element:

  `IsTerminal A ↔ ∀ B, S.RecordEquivalent B.T A.T`

Combined with `optimal_unique_up_to_iso` (FinalityTheorem.lean, zero sorry), this gives:
the unique PSC-optimal theory is the terminal object of PSCSys. GTE is that theory
(Stage 3: `GTEOptimalityInstance.lean`, zero sorry). This is the categorical content of C1.

## Certification status

| Component | Status |
|---|---|
| `PSCCompatibleSpace` | structural definition |
| `PSCSubstrate` | structural definition |
| `instCategory` (PSCSys Category) | zero sorry |
| `IsTerminal` | zero sorry |
| `IsTerminal.unique_up_to_iso` | zero sorry |
-/

/-- A theory space in which `RecordEquivalent` is a preorder (reflexive and transitive).
    This is the minimum structure needed for PSCSys to be a well-defined category.
    `GTECompatibleSpace` (in GTEOptimalityInstance.lean) is the concrete instance. -/
structure PSCCompatibleSpace extends TheorySpace where
  /-- Record equivalence is reflexive: every theory is equivalent to itself. -/
  req_refl  : ∀ T, RecordEquivalent T T
  /-- Record equivalence is transitive. -/
  req_trans : ∀ T1 T2 T3, RecordEquivalent T1 T2 → RecordEquivalent T2 T3 →
              RecordEquivalent T1 T3

/-- A PSC-consistent arithmetic substrate: a PSC-compatible theory space with a
    PSC-optimal theory in that space. These are the **objects** of PSCSys. -/
structure PSCSubstrate (S : PSCCompatibleSpace) where
  /-- The canonical theory of this substrate. -/
  T       : S.Theory
  /-- PSC-optimality: `T` minimizes descriptional complexity among all
      record-equivalent theories. -/
  optimal : TheorySpace.PSCOptimal S.toTheorySpace T

namespace PSCSubstrate

variable {S : PSCCompatibleSpace}

/-- `PLift P` for `P : Prop` is a subsingleton: any two elements are equal by
    propositional irrelevance. This makes all categorical laws trivial for our Hom-sets. -/
private instance pLiftSubsingleton {P : Prop} : Subsingleton (PLift P) :=
  ⟨fun ⟨h1⟩ ⟨h2⟩ => congrArg PLift.up (proof_irrel h1 h2)⟩

/-- **PSCSys is a (thin) category.**

    A morphism `A ⟶ B` is a proof (wrapped in `PLift`) that `A.T` and `B.T` are
    record-equivalent. Since each Hom-set is a subsingleton, all categorical laws
    (identity, associativity) hold by `Subsingleton.elim`.

    Physical interpretation of morphisms: a PSC-morphism `A → B` witnesses that
    the arithmetic substrate `B` records everything that `A` records — both are
    informationally equivalent at the PSC level. -/
instance instCategory : Category (PSCSubstrate S) where
  Hom  A B := PLift (S.RecordEquivalent A.T B.T)
  id   A   := ⟨S.req_refl A.T⟩
  comp f g := ⟨S.req_trans _ _ _ f.down g.down⟩
  id_comp  := fun _ => Subsingleton.elim _ _
  comp_id  := fun _ => Subsingleton.elim _ _
  assoc    := fun _ _ _ => Subsingleton.elim _ _

/-! ### Terminal object in PSCSys -/

/-- A substrate `A` is terminal in PSCSys iff there is a unique PSC-morphism
    `B ⟶ A` for every substrate `B`. In the thin category, this reduces to:
    `A.T` is record-equivalent to every other PSC-optimal theory.

    **C1 statement**: GTE's theory (`fmdl`) is terminal in PSCSys. -/
def IsTerminal (A : PSCSubstrate S) : Prop :=
  ∀ B : PSCSubstrate S, S.RecordEquivalent B.T A.T

/-- In a thin category, all morphisms between any two fixed objects are equal
    (uniqueness is automatic by `Subsingleton`). -/
theorem hom_subsingleton {A B : PSCSubstrate S}
    (f g : PLift (S.RecordEquivalent A.T B.T)) : f = g :=
  Subsingleton.elim f g

/-- Two terminal objects are record-equivalent (unique up to isomorphism in PSCSys). -/
theorem IsTerminal.unique_up_to_iso {A B : PSCSubstrate S}
    (_ : IsTerminal A) (hB : IsTerminal B) : S.RecordEquivalent A.T B.T :=
  hB A

/-- A terminal object admits a canonical PSC-morphism from any substrate. -/
def IsTerminal.toMorphism {A B : PSCSubstrate S}
    (hB : IsTerminal B) : PLift (S.RecordEquivalent A.T B.T) :=
  ⟨hB A⟩

end PSCSubstrate

end NemS.Category
