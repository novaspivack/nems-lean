import SemanticNonlocality.Core.LocalityAxioms
import Closure.Core.ObsSemantics

/-!
# SemanticNonlocality.Examples.ToyFactorization

**Paper 45: Toy factorized semantics.**

World = two fragments (Fin 2), each with a Boolean local view. Observables are
**per-fragment claims** (f, b): "fragment f has value b". Holds w (f', b) iff w(f') = b.
Local predicate: at fragment f, localHolds(f, ℓ, (f', b)) = (if f = f' then ℓ = b else True).
Global Holds is the conjunction of these local claims; factorization holds by construction.
-/

set_option autoImplicit false

namespace SemanticNonlocality

open Closure.ObsSemantics

def ToyWorld : Type := Fin 2 → Bool
def ToyFragment : Type := Fin 2
def ToyLocalWorld : Type := Bool
/-- Observables as per-fragment claims: (fragment, value). -/
def ToyObs : Type := ToyFragment × Bool

def toyHolds (w : ToyWorld) (o : ToyObs) : Prop := w o.1 = o.2

def toySemantics : Closure.ObsSemantics ToyWorld ToyObs where
  Holds := toyHolds

def toyRestrict (w : ToyWorld) (f : ToyFragment) : ToyLocalWorld := w f

/-- localHolds(f, ℓ, (f', b)) := if f = f' then ℓ = b else True. -/
def toyLocalHolds (f : ToyFragment) (l : ToyLocalWorld) (o : ToyObs) : Prop :=
  f ≠ o.1 ∨ l = o.2

theorem toy_factorized (w : ToyWorld) (o : ToyObs) :
    toySemantics.Holds w o ↔ ∀ f : ToyFragment, toyLocalHolds f (toyRestrict w f) o := by
  simp only [toySemantics, toyHolds, toyRestrict, toyLocalHolds]
  constructor
  · intro h f; by_cases heq : f = o.1 <;> simp [heq, h]
  · intro h; exact (h o.1).elim (fun ne => (ne rfl).elim) id

def toyLocality : LocalityAxioms toySemantics where
  Fragment := ToyFragment
  LocalWorld := ToyLocalWorld
  restrict := toyRestrict
  localHolds := toyLocalHolds
  factorized := toy_factorized

/-- Toy witnesses same local views ⇒ obs equiv. -/
theorem toy_same_views_obs_equiv (w₁ w₂ : ToyWorld) (h : ∀ f, toyRestrict w₁ f = toyRestrict w₂ f) :
    toySemantics.ObsEquiv w₁ w₂ :=
  same_local_views_imp_obs_equiv toySemantics toyLocality w₁ w₂ h

end SemanticNonlocality
