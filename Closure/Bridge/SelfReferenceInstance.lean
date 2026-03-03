import Closure.Core.Internal
import SelfReference.Core.Interface

/-!
# Closure.Bridge.SelfReferenceInstance

**A0 Bridge: Closure ↔ SelfReference**

When a theory has **internal representability** it yields an SRI instance:
- **TheoryWithRepr** (repr-spec only) → SRI₀′, so MFP-1 applies (Gödel-level).
- **TheoryWithReprPlus** (+ eval_quote) → SRI′, so the full interface and
  unityped corollary/barrier apply (Kleene/NEMS-level).

This keeps the bridge aligned with Paper 26: repr-spec is minimal for the
diagonal lemma; eval_quote is the re-entry extension.
-/

set_option autoImplicit false

namespace Closure

universe u v

/-- **Theory with repr (minimal).**  Repr-spec only; yields SRI₀′ and hence MFP-1. -/
structure TheoryWithRepr (Obj : Type u) (Code : Type v) where
  Equiv       : Obj → Obj → Prop
  equiv_refl  : ∀ x, Equiv x x
  equiv_symm  : ∀ {x y}, Equiv x y → Equiv y x
  equiv_trans : ∀ {x y z}, Equiv x y → Equiv y z → Equiv x z
  quote       : Obj → Code
  run         : Code → Code → Obj
  repr        : (Code → Obj) → Code
  repr_spec   : ∀ (F : Code → Obj) (c : Code), Equiv (run (repr F) c) (F c)

/-- **Theory with repr and re-entry.**  Extends TheoryWithRepr with eval_quote; yields SRI′. -/
structure TheoryWithReprPlus (Obj : Type u) (Code : Type v) extends TheoryWithRepr Obj Code where
  eval_quote : ∀ (x : Obj), Equiv (run (quote x) (quote x)) x

/-- Minimal internal representability → SRI₀′.  MFP-1 (two-sorted) applies. -/
instance theoryWithRepr_to_SRI0' (Obj : Type u) (Code : Type v) (T : TheoryWithRepr Obj Code) :
    SelfReference.SRI0' Obj Code where
  Equiv       := T.Equiv
  equiv_refl  := T.equiv_refl
  equiv_symm  := T.equiv_symm
  equiv_trans := T.equiv_trans
  quote       := T.quote
  run         := T.run
  repr        := T.repr
  repr_spec   := T.repr_spec

/-- Repr + re-entry → SRI′.  Full fixed-point corollary and barrier apply. -/
instance theoryWithReprPlus_to_SRI' (Obj : Type u) (Code : Type v) (T : TheoryWithReprPlus Obj Code) :
    SelfReference.SRI' Obj Code where
  Equiv       := T.Equiv
  equiv_refl  := T.equiv_refl
  equiv_symm  := T.equiv_symm
  equiv_trans := T.equiv_trans
  quote       := T.quote
  run         := T.run
  repr        := T.repr
  repr_spec   := T.repr_spec
  eval_quote  := T.eval_quote

end Closure
