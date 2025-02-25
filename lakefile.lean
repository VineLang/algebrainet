import Lake
open Lake DSL

package "algebrainet" where
  -- add package configuration options here

lean_lib «Algebrainet» where
  -- add library configuration options here

@[default_target]
lean_exe "algebrainet" where
  root := `Main
