import Lake
open Lake DSL

package "Kura" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib"
require "apnelson1" / "Matroid"

@[default_target]
lean_lib «Kura» where
  -- add any library configuration options here
