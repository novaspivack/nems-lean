import NemS.Adjudication.Basic
import NemS.Adjudication.NoEmulation

/-!
# NemS.Adjudication

**Paper 15 (C1): No-Emulation / Self-Necessitating Adjudication.**

This module family proves that internal adjudication (PT / Transputation)
is necessarily non-emulable in diagonal-capable frameworks.

## Module structure

- `NemS.Adjudication.Basic`       — `ChoicePointInterface`, `AdjudicationFn`
- `NemS.Adjudication.NoEmulation` — `no_emulation`, `adjudication_necessity`

## Main theorems

- `no_emulation`: no total computable function can emulate PT on all states.
- `adjudication_necessity`: active internal selection cannot be replaced by
  any static algorithm.
-/
