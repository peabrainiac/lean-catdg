import Lake
open Lake DSL

package «CatDG» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩, -- switch off auto-implicit
    ⟨`relaxedAutoImplicit, false⟩, -- switch off relaxed auto-implicit
    ⟨`linter.style.longLine, true⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.23.0"

@[default_target]
lean_lib «CatDG» where
  -- add any library configuration options here
