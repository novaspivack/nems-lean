import NemS.Core.ObsEq

/-! # NemS.Core.Categoricity -/

namespace NemS
namespace Framework

variable (F : Framework)

def ObsCategorical : Prop :=
  ∀ M N : F.Model, F.ObsEq M N

theorem obsCategorical_iff_subsingleton :
    F.ObsCategorical ↔ Subsingleton F.WorldTypes := by
  constructor
  · intro h
    constructor
    intro q₁ q₂
    induction q₁ using Quotient.inductionOn with | h M => ?_
    induction q₂ using Quotient.inductionOn with | h N => ?_
    exact Quotient.sound (h M N)
  · intro ⟨hss⟩ M N
    have : F.toWorldType M = F.toWorldType N := hss _ _
    exact (F.toWorldType_eq_iff).mp this

theorem obsCategorical_worldTypes_eq (h : F.ObsCategorical)
    (q₁ q₂ : F.WorldTypes) : q₁ = q₂ :=
  (F.obsCategorical_iff_subsingleton.mp h).elim q₁ q₂

/-- Non-categoricity: there exist M, N, r with M and N disagreeing on r. -/
theorem not_obsCategorical_iff :
    ¬ F.ObsCategorical ↔
    ∃ M N : F.Model, ∃ r : F.Rec,
      (F.Truth M r ∧ ¬ F.Truth N r) ∨ (¬ F.Truth M r ∧ F.Truth N r) := by
  constructor
  · intro hNC
    -- Unfold to get ∃ M N r, ¬ (Truth M r ↔ Truth N r)
    simp only [ObsCategorical, ObsEq, not_forall] at hNC
    obtain ⟨M, N, r, hr⟩ := hNC
    -- hr : ¬ (F.Truth M r ↔ F.Truth N r)
    rcases Classical.em (F.Truth M r) with hM | hM
    · rcases Classical.em (F.Truth N r) with hN | hN
      · exact absurd (Iff.intro (fun _ => hN) (fun _ => hM)) hr
      · exact ⟨M, N, r, Or.inl ⟨hM, hN⟩⟩
    · rcases Classical.em (F.Truth N r) with hN | hN
      · exact ⟨M, N, r, Or.inr ⟨hM, hN⟩⟩
      · exact absurd (Iff.intro (fun h => absurd h hM) (fun h => absurd h hN)) hr
  · rintro ⟨M, N, r, (⟨hM, hN⟩ | ⟨hM, hN⟩)⟩ hcat
    · exact hN ((hcat M N r).mp hM)
    · exact hM ((hcat M N r).mpr hN)

end Framework
end NemS
