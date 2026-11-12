import Lake
open Lake DSL

package FrohmanianTether where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0-rc1"

@[default_target]
lean_lib FrohmanianTether where

/-- Scratch work (not a default target). `lake build Scratch` compiles every
`Scratch/*.lean` module via the submodule glob (no root `Scratch.lean`).
Individual modules: `lake build Scratch.R3BKMContinuation`. -/
lean_lib Scratch where
  globs := #[.submodules `Scratch]
