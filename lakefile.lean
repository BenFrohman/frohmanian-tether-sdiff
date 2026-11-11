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

/-- Dependencies of the vendored classical-continuation pillar (`vendor/BKMPillar`), pinned to
the revisions used by `BenFrohman/periodic-ns-classical-continuation` @ `502ff17`. -/
require TorusFourierNS from git
  "https://github.com/BenFrohman/torus-fourier-ns-lemmas.git" @ "e63af4ea9bd3849ee7a0e6d9a7b64a0751d12fbe"

require WeightedEnstrophy from git
  "https://github.com/BenFrohman/weighted-enstrophy-identities.git" @ "1df4652d1a40430055ba6480904db5ab270497c3"

@[default_target]
lean_lib FrohmanianTether where

/-- Non-module bridge files that import proved pillar repositories (kept out of the `module`
library `FrohmanianTether`, which may only import modules). -/
@[default_target]
lean_lib FrohmanianTetherPillars where
  roots := #[`FrohmanianTether.Pillars]

/-- Vendored, namespace-renamed copy of the proved classical-continuation pillar (BKM criterion,
Kato local existence, maximal solution): `BenFrohman/fefferman-clay-navier-stokes` @ `ebcf109` and
`BenFrohman/periodic-ns-classical-continuation` @ `502ff17`, with the namespace `NavierStokes3D`
renamed to `FeffermanNavierStokes3D` and module prefixes moved under `BKMPillar` (see
`vendor/BKMPillar/VENDOR.md` and `scripts/check_vendor.sh`). The rename is needed because both
upstream repositories declare `NavierStokes3D.*` names that clash with this library's. -/
@[default_target]
lean_lib BKMPillar where
  srcDir := "vendor"
  roots := #[`BKMPillar.PeriodicNSContinuation.IntegrabilityAttack]
  globs := #[.submodules `BKMPillar]
