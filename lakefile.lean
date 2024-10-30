import Lake
open Lake DSL

package "Slotted" where
  -- add package configuration options here

lean_lib «Slotted» where
  -- add library configuration options here

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.12.0"

@[default_target]
lean_exe "slotted" where
  root := `Main
