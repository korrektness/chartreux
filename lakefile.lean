import Lake
open Lake DSL

package flow {
  -- add package configuration options here
}

lean_lib Flow {
  -- add library configuration options here
}

@[default_target]
lean_exe flow {
  root := `Main
}
