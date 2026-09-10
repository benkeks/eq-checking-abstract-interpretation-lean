import Lake
open Lake DSL

package EqCheckingAbstractInterpretation where
  -- add any package configuration options here

lean_lib EqCheckingAbstractInterpretation where
  -- add any library configuration options here

@[default_target]
lean_exe Main where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"
