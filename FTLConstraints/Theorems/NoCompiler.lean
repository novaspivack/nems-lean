import SelectorStrength.Theorems.BarrierSchema
import SelectorStrength.Core.Deciders
import SelectorStrength.Instances.Trivial
import FTLConstraints.Core.CorrelationVsSignal

/-!
# FTLConstraints.Theorems.NoCompiler

**Paper 47: No spooky-to-signal compiler.**

A spooky-to-signal compiler for T (paper definition: total decider for T) cannot exist
under diagonal capability: the Paper 29 barrier forbids any total decider for an
extensional nontrivial T. Theorem stated as ¬ SpookyToSignalCompiler S_all T to match
the paper's formal story.
-/

set_option autoImplicit false

namespace FTLConstraints

universe u

variable {α : Type u} (Equiv : α → α → Prop)

open SelectorStrength

/-- **No spooky-to-signal compiler (schema).** Under the barrier assumptions,
no spooky-to-signal compiler for T exists at S_all (i.e. no total decider for T). -/
theorem no_spooky_to_signal_compiler
    (T : α → Prop)
    (hExt : Extensional Equiv T)
    (hNontriv : Nontrivial T)
    (hFP : ∀ F : α → α, ∃ d : α, Equiv d (F d)) :
    ¬ SpookyToSignalCompiler (S_all (α := α)) T := by
  rw [spookyToSignalCompiler_iff_decidableAt]
  exact no_total_decider_all Equiv T hExt hNontriv hFP

end FTLConstraints
