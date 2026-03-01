import NemS.Quantum.BuschGleason

/-!
# NemS.Quantum.BornFromPSC

Born rule from PSC closure.

The Busch/Gleason theorem (BuschGleason.lean) gives:
  EffectMeasure → ∃ ρ, μ(E) = Re(Tr(ρE))

This module connects that to PSC: the claim is that PSC + semantic
visibility forces probability assignments to be EffectMeasures
(noncontextual and additive on POVMs).

The PSC→EffectMeasure step is stated as a physical hypothesis here;
the math core is the representation theorem.
-/

namespace NemS
namespace Quantum

/-- **Born Rule from PSC (top-level statement).**

Under the physical hypothesis that PSC forces probability assignments
to be EffectMeasures (normalized, additive, noncontextual), the Born
rule follows from the Busch/Gleason representation theorem. -/
theorem born_rule_from_psc {n : ℕ} (m : EffectMeasure n) :
    ∃ ρ : DensityOp n, ∀ E : Effect n, m.μ E = (opTrace (ρ.ρ * E.op)).re :=
  busch_gleason m

/-- **Born Rule for projectors from PSC.** -/
theorem born_rule_projectors_from_psc {n : ℕ} (m : EffectMeasure n) :
    ∃ ρ : DensityOp n, ∀ (P : Effect n), P.op * P.op = P.op →
      m.μ P = (opTrace (ρ.ρ * P.op)).re := by
  obtain ⟨ρ, hρ⟩ := busch_gleason m
  exact ⟨ρ, fun P _ => hρ P⟩

end Quantum
end NemS
