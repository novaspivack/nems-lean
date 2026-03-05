import SelectorStrength.Core.Strength
import SelectorStrength.Core.Deciders

/-!
# FTLConstraints.Core.CorrelationVsSignal

**Paper 47: Correlation vs. signal interfaces.**

- **Correlation** (here): type α encoding correlation data (e.g. local-view maps, world-type codes).
- **Signal**: controllable output; we use Bool as the canonical signal type.
- **Spooky-to-signal compiler for T**: a total-effective map C : α → Bool at strength Sbool that
  is a **total decider** for T (∀ x, C x = true ↔ T x). So "no compiler" = no total decider
  at that strength (Paper 29 barrier). Definition matches the paper to avoid "mere correlation" loophole.
-/

set_option autoImplicit false

namespace FTLConstraints

universe u

variable {α : Type u}

open SelectorStrength

/-- **Signal** type: the controllable output (e.g. Bool). -/
def Signal := Bool

/-- A **compiler** from correlation α to signal is a map α → Signal. -/
def Compiler (α : Type u) := α → Signal

/-- A compiler **decides** predicate T when it is a total decider for T (C x = true ↔ T x). -/
def CompilerDecides (T : α → Prop) (C : Compiler α) : Prop :=
  TotalDecider T (fun x => C x)

/-- **Spooky-to-signal compiler for T at strength Sbool**: exists a total decider for T in Sbool.
Matches paper definition: compiler = total decider for T, not merely correlated. -/
def SpookyToSignalCompiler (Sbool : Strength α Bool) (T : α → Prop) : Prop :=
  ∃ C : α → Bool, Sbool C ∧ TotalDecider T C

/-- SpookyToSignalCompiler is equivalent to DecidableAt (same witnesses). -/
theorem spookyToSignalCompiler_iff_decidableAt (Sbool : Strength α Bool) (T : α → Prop) :
    SpookyToSignalCompiler Sbool T ↔ DecidableAt Sbool T :=
  ⟨fun ⟨C, hS, hDec⟩ => ⟨C, hS, hDec⟩, fun ⟨δ, hS, hDec⟩ => ⟨δ, hS, hDec⟩⟩

end FTLConstraints
