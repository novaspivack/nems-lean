import NemS.Prelude

/-!
# Sieve.Core.TheorySpace

**Theory space (Paper 34).**

A type of candidates α with optional equivalence and canonicalization.
Used as the base for the sieve engine: constraints live on this space.
-/

set_option autoImplicit false

namespace Sieve

universe u

/-- A theory space: type of candidates with optional equivalence and canon. -/
structure TheorySpace (α : Type u) where
  /-- Equivalence on candidates (e.g. equivalence of theories). -/
  Equiv : α → α → Prop
  /-- Optional: canonical representative (canon a ≈ a; canon a₁ = canon a₂ ↔ a₁ ≈ a₂). -/
  canon : Option (α → α)

end Sieve
