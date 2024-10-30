import Lake
open Lake DSL

package "Slotted" where
  -- add package configuration options here

lean_lib «Slotted» where
  -- add library configuration options here

@[default_target]
lean_exe "slotted" where
  root := `Main
