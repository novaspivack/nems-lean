/-!
# SelectorStrength.Instances.ComputableNatConcrete (intended)

**Fully instantiated computable barrier (Paper 29 — future direction).**

This file is a placeholder for the flagship nontrivial instance: strength = Mathlib
`Computable` on Nat, with hFP supplied by `Nat.Partrec.Code.fixed_point` (Rogers)
or the recursion theorem. The goal is:

- Define `S_comp_bool : Strength Nat Bool` by `S_comp_bool δ := Computable δ`
- Define `S_comp_α : Strength Nat Nat` by `S_comp_α F := Computable F`
- Prove `AntiDeciderClosed S_comp_bool S_comp_α` (if δ and constants are computable,
  then λ x => if δ x then f₀ else t₀ is computable)
- Prove hFP for computable total F : Nat → Nat (every such F has a fixed point;
  this requires connecting Mathlib's `Nat.Partrec.Code.fixed_point`, which is for
  code-to-code maps, to the statement ∀ F, Computable F → ∃ d, F d = d)
- Conclude `no_total_decider_nat` with Equiv = Eq: ¬∃ computable total δ deciding T

Until then, use `SelectorStrength.Instances.ComputableNat` (template with parametric
hFP). See Paper 29 §5.2 and Future directions.
-/

-- TODO: Implement when Mathlib connection from Computable (Nat → Nat) to
-- Nat.Partrec.Code.fixed_point (or a direct total fixed-point lemma) is available.
-- Required: AntiDeciderClosed for Computable; hFP for total Computable F; then
-- no_total_decider_nat Eq S_comp_bool S_comp_α ...

set_option autoImplicit false
