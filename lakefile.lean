import Lake
open Lake DSL

package «nems-lean» where
  -- GPTClosure (Paper 39), InstitutionalEpistemics (Paper 40)

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.14.0"

@[default_target]
lean_lib «GPTClosure» where
  -- Paper 39

lean_lib «InstitutionalEpistemics» where
  -- Paper 40
