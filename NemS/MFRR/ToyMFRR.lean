import NemS.MFRR.BridgeToNEMS
import NemS.Examples.Toy

/-!
# NemS.MFRR.ToyMFRR

Toy instantiation demonstrating the MFRR bridge on the Bool framework
from `NemS.Examples.Toy`.

The Bool framework has `Model := Bool`, `Rec := Bool`, `Truth M r := (M = r)`.
It is non-categorical (true ≠ false as models).  We construct:

1. A `ChoiceData` with a single choice point having two branches (true, false).
2. A proof that this constitutes `HasRecordDivergentChoice`.
3. A `PSCBundle` (using a trivially-satisfiable internality predicate).
4. Application of the bridge theorem to extract PT.

This demonstrates the full pipeline: choice data → non-categoricity →
NEMS forces internal selector → PT exists.
-/

namespace NemS.MFRR.ToyMFRR

open NemS
open NemS.Framework
open NemS.MFRR
open NemS.Examples

/-! ## The Bool framework (from NemS.Examples.Toy) -/

/-- The Bool framework: `Model := Bool`, `Rec := Bool`, `Truth M r := (M = r)`. -/
noncomputable def F : Framework := boolFramework

/-! ## Choice data: a single choice point with two branches -/

/-- Choice data for the Bool framework: one choice point at `true`,
with branches `{true, false}`. -/
def boolChoiceData : ChoiceData boolFramework where
  CP := fun _ => Unit
  branches := fun _ => {true, false}
  nonempty := fun _ => ⟨true, Set.mem_insert true {false}⟩

/-! ## Record-divergent choice -/

/-- The Bool framework has record-divergent choice: `true` and `false`
disagree on the record statement `true`. -/
theorem bool_has_divergent_choice :
    HasRecordDivergentChoice boolFramework boolChoiceData := by
  refine ⟨true, (), true, false, ?_, ?_, ?_⟩
  · exact Set.mem_insert true {false}
  · exact Set.mem_insert_iff.mpr (Or.inr rfl)
  · intro h
    have := (h true).mp rfl
    exact Bool.noConfusion this

/-! ## Constructing a PSCBundle -/

/-- A trivially-satisfiable internality predicate: every selector is internal.
This is the weakest possible predicate, used here to demonstrate the
pipeline without committing to a specific internality notion. -/
def trivialInternal : boolFramework.Selector → Prop := fun _ => True

/-- In the Bool framework, ObsEq implies equality of models.
Since `Truth M r := (M = r)`, if `∀ r, (M = r ↔ N = r)` then in
particular `(M = M ↔ N = M)`, so `N = M`. -/
theorem bool_obsEq_implies_eq {M N : Bool} (h : boolFramework.ObsEq M N) : M = N := by
  have := (h M).mp rfl
  simp [boolFramework] at this
  exact this.symm

/-- The Bool framework satisfies NEMS under trivial internality.
We use the identity as a selector: since ObsEq implies equality in
this framework, `id` satisfies all selector axioms. -/
theorem bool_nems : NEMS boolFramework trivialInternal := by
  intro ⟨_, hNoSel⟩
  apply hNoSel
  refine ⟨⟨id,
    fun _ => ObsEq.refl _,
    fun _ => rfl,
    fun h => ?_⟩, trivial⟩
  exact congrArg id (bool_obsEq_implies_eq h)

/-- DeterminacyPSC for the Bool framework (trivially, since we use
the weakest internality predicate). -/
theorem bool_detPSC : boolFramework.DeterminacyPSC := by
  intro dep IsInternal hNEMS
  rcases nems_implies_cat_or_internal hNEMS with hcat | hsel
  · exact absurd hcat (boolFramework.er_non_categorical dep)
  · exact hsel

/-- The PSC bundle for the Bool framework. -/
def boolPSC : PSCBundle boolFramework trivialInternal where
  nems := bool_nems
  detPSC := bool_detPSC

/-! ## Applying the bridge theorem -/

/-- **Main demonstration:** the bridge theorem extracts PT from the
Bool framework's PSC bundle and choice data. -/
theorem bool_PT_exists :
    ∃ _pt : PT boolFramework trivialInternal, True :=
  PSC_and_choice_force_PT boolPSC boolChoiceData bool_has_divergent_choice

/-- Extract the internal selector directly. -/
theorem bool_internal_selector_exists :
    ∃ S : boolFramework.Selector, trivialInternal S :=
  PSC_and_choice_force_internal_selector boolPSC boolChoiceData bool_has_divergent_choice

end NemS.MFRR.ToyMFRR
