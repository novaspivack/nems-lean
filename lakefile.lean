import Lake
open Lake DSL

package nems where
  name := `nems

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib NemS where
  globs := #[.submodules `NemS]
