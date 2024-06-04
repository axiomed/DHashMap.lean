import Lake
open Lake DSL

package «DHashMap» where
  -- add package configuration options here

lean_lib «DHashMap» where
  -- add library configuration options here

@[default_target]
lean_exe «dhashmap» where
  root := `Main
