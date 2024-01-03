import Lake
open Lake DSL

package «nat-cov-recursion» where
  -- add package configuration options here

lean_lib «NatCovRecursion» where
  -- add library configuration options here

@[default_target]
lean_exe «nat-cov-recursion» where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"089e95fb3b3ae586e821f77cd172c1bc01f70acd"
