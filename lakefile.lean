import Lake
open Lake DSL

package FrohmanianTether where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0-rc1"

/-- Proved pillar: uniqueness of classical `ℤ³`-periodic Navier–Stokes solutions
(`BenFrohman/periodic-navier-stokes-smooth-uniqueness`, same Lean toolchain and Mathlib rev). -/
require NSTorusUniqueness from git
  "https://github.com/BenFrohman/periodic-navier-stokes-smooth-uniqueness.git" @ "de92662d45e8a0f47ce0c196f6dbcfe44ddb4b3b"

@[default_target]
lean_lib FrohmanianTether where

/-- Non-module bridge files that import proved pillar repositories (kept out of the `module`
library `FrohmanianTether`, which may only import modules). -/
@[default_target]
lean_lib FrohmanianTetherPillars where
  roots := #[`FrohmanianTether.Pillars]
