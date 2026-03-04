import Lake
open Lake DSL

package nems where
  name := `nems

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"

@[default_target]
lean_lib NemS where
  globs := #[.submodules `NemS]

lean_lib SelfReference where
  globs := #[.submodules `SelfReference]

lean_lib Closure where
  globs := #[.submodules `Closure]

lean_lib Reflection where
  globs := #[.submodules `Reflection]

lean_lib SelectorStrength where
  globs := #[.submodules `SelectorStrength]

lean_lib Learning where
  globs := #[.submodules `Learning]

lean_lib EpistemicAgency where
  globs := #[.submodules `EpistemicAgency]

lean_lib SelfImprovement where
  globs := #[.submodules `SelfImprovement]

lean_lib SelfAwareness where
  globs := #[.submodules `SelfAwareness]
