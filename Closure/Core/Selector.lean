import Closure.Core.ObsSemantics

/-!
# Closure.Core.Selector

A selector is a section of the quotient map: it picks a canonical
representative world for each world-type.  This is the "completion
ingredient" of the Closure Calculus — when multiple world-types exist,
a selector resolves the choice.

No Choice axiom is used in the core: we work with "if a selector exists, then …".
-/

set_option autoImplicit false

namespace Closure

universe u v

variable {World : Type u} {Obs : Type v} (S : ObsSemantics World Obs)

/-- A **selector** for observational semantics `S` is a section of the
quotient map: `sel t` is a world in the equivalence class `t`, and
`toWorldType (sel t) = t`. -/
structure Selector where
  /-- The section: each world-type gets a representative world. -/
  sel : S.WorldType → World
  /-- Section property: the representative lies in the correct class. -/
  sec : ∀ t : S.WorldType, S.toWorldType (sel t) = t

namespace Selector

variable {S} (sel : Selector S)

/-- The selector's representative for a world `w` is observationally
equivalent to `w`. -/
theorem sel_obs_equiv (w : World) :
    S.ObsEquiv (sel.sel (S.toWorldType w)) w :=
  (S.toWorldType_eq_iff (sel.sel (S.toWorldType w)) w).mp (sel.sec (S.toWorldType w))

/-- Two worlds in the same world-type get the same selector image. -/
theorem same_type_same_sel (w₁ w₂ : World)
    (h : S.toWorldType w₁ = S.toWorldType w₂) :
    sel.sel (S.toWorldType w₁) = sel.sel (S.toWorldType w₂) := by
  rw [h]

end Selector

/-- **Categoricity-or-selector dichotomy (generic).**
If there is at most one world-type, no selector is needed in the sense
that any world is a "canonical" representative.  If there is more than
one world-type, any total completion function that picks a world for
each type gives a selector (we state existence: given a function that
assigns to each world-type a world in that class, we have a selector). -/
theorem selector_of_lift
    (f : S.WorldType → World)
    (hf : ∀ t, S.toWorldType (f t) = t) :
    Nonempty (Selector S) :=
  ⟨⟨f, hf⟩⟩

/-- A predicate **chooses a representative** when it picks exactly one
world per world-type: every class has some world satisfying P, and
observationally equivalent worlds satisfying P are equal. -/
structure ChoosesRep (P : World → Prop) : Prop where
  exists_in_each : ∀ t : S.WorldType, ∃ w : World, S.toWorldType w = t ∧ P w
  unique_in_type : ∀ {w₁ w₂ : World}, S.ObsEquiv w₁ w₂ → P w₁ → P w₂ → w₁ = w₂

/-- Under `ChoosesRep S P`, each world-type has a unique world satisfying P. -/
theorem ChoosesRep.unique_per_type (P : World → Prop) (h : ChoosesRep S P) (t : S.WorldType) :
    ∃! w : World, S.toWorldType w = t ∧ P w := by
  obtain ⟨w, heq, hP⟩ := h.exists_in_each t
  refine ⟨w, ⟨heq, hP⟩, ?_⟩
  intro w' ⟨heq', hP'⟩
  have hobs : S.ObsEquiv w w' := (S.toWorldType_eq_iff w w').mp (heq.trans heq'.symm)
  exact h.unique_in_type (ObsSemantics.ObsEquiv.symm S hobs) hP' hP

/-- **Selector extraction from a choice predicate.**  If P chooses a
representative (one per world-type), we can build a selector without
global Choice by using the unique witness per class. -/
theorem selector_of_choice_pred (P : World → Prop) (h : ChoosesRep S P) :
    Nonempty (Selector S) := by
  let sel : S.WorldType → World := fun t => Classical.choose (h.exists_in_each t)
  have hsec : ∀ t, S.toWorldType (sel t) = t := by
    intro t
    exact (Classical.choose_spec (h.exists_in_each t)).1
  exact selector_of_lift S sel hsec

end Closure
