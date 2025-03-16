import Lake
open Lake DSL

package «operad» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.17.0"

@[default_target]
lean_lib «Operad» {
  -- add any library configuration options here
}
