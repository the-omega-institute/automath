import Lake
open Lake DSL

package "Omega" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`maxHeartbeats, 400000⟩  -- per-file compilation time guard
  ]

require "leanprover-community" / "mathlib" @ git "v4.28.0"

@[default_target]
lean_lib «Omega» where
  -- add any library configuration options here
