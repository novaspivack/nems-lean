import Lake
open Lake DSL

package «nems-lean» where
  -- GPTClosure (Paper 39), InstitutionalEpistemics (Paper 40)

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc3"

@[default_target]
lean_lib «GPTClosure» where
  -- Paper 39

lean_lib «InstitutionalEpistemics» where
  -- Paper 40

lean_lib «NemS» where
lean_lib «Closure» where
lean_lib «SelfReference» where
  -- Paper 26: SRI, MFP-1, MFP-2
lean_lib «Reflection» where
  -- Paper 28: SRI_R, DiagClosed, restricted_master_fixed_point
lean_lib «SelectorStrength» where
lean_lib «SemanticSelfDescription» where
  -- Necessary Incompleteness of Internal Semantic Self-Description
lean_lib «ArrowOfTime» where
lean_lib «RefinementFlow» where
lean_lib «RecordEntropy» where
lean_lib «ErrorCorrectingClosure» where
  -- Paper 43

lean_lib «LawCalibration» where
  -- Paper 44

lean_lib «SemanticNonlocality» where
  -- Paper 45

lean_lib «CausalNonlocality» where
  -- Paper 46

lean_lib «FTLConstraints» where
  -- Paper 47

lean_lib «HolographyUnderClosure» where
  -- Paper 48

lean_lib «CertificationLogic» where
  -- Paper 50 (capstone). Depends on InstitutionalEpistemics (Role) and SelectorStrength (barrier).
  -- For a standalone CertificationLogic build, run: lake build InstitutionalEpistemics SelectorStrength CertificationLogic
  -- or use full build: lake build
